import DirectedFlowCutGap.ResidualRowUpdateProgram
import DirectedFlowCutGap.ResidualMatrixProgram

/-!
# Updating the represented flow matrix along a residual path

Each row is paired with its source label. The scanner constructs that row's
context from the shared path and column labels. Its result uses the same
table representation as the input, so another residual scan can consume it.
-/

namespace DirectedFlowCutGap.ResidualTableUpdateProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor GraphWalkExtension
open ResidualRowProgram (Entry StoredRow row_extend)
open ResidualMatrixProgram (StoredTable ValueTable)
open GraphDiscoveryProgram (Vertices vertices_extend)
open BinarySigned (Canonical decode)

def rowLabel (pc : Fin 448) : Fin 480 := ⟨32+pc.val,by omega⟩

def program : Program 480 := fun pc =>
  if pc.val<32 then
    match pc.val with
    | 0 => .branch .r0 1 27 27 4
    | 1 => .make .r3 .nil 2
    | 2 => .ret .r3
    | 4 => .field .r3 .r0 false 5
    | 5 => .field .r0 .r0 true 6
    | 6 => .call 12 7 .r0
    | 7 => .call 16 8 .r3
    | 8 => .make .r3 (.pair .r3 .r0) 2
    | 12 => .field .r1 .r1 true 13
    | 13 => .call 0 14 .r3
    | 14 => .ret .r3
    | 16 => .move .r0 .r3 17
    | 17 => .field .r3 .r1 false 18
    | 18 => .field .r1 .r2 true 19
    | 19 => .field .r2 .r2 false 20
    | 20 => .make .r2 (.pair .r2 .r3) 21
    | 21 => .call (rowLabel 22) 22 .r3
    | 22 => .ret .r3
    | 26 => .call 0 27 .r3
    | _ => .halt
  else if pc.val=55 then .ret .r3
  else ReferenceProgramLabels.instruction rowLabel
    (ResidualRowUpdateProgram.program ⟨pc.val-32,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 480))
    (tape : Bits) (pc : Fin 480) : NaturalState 480 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def Context (heap : NaturalHeap) (root : ℕ) (es : List (Bits×Bits)) (vs : List Bits) : Prop :=
  ∃ path columns,heap[root]?=some (.pair path columns) ∧ EdgeList heap path es ∧ Vertices heap columns vs

theorem context_extend {heap : NaturalHeap} {root : ℕ} {es : List (Bits×Bits)} {vs : List Bits}
    (h : Context heap root es vs) (ext : NaturalHeap) : Context (heap++ext) root es vs := by
  obtain ⟨path,columns,hp,he,hv⟩ := h
  exact ⟨path,columns,lookup_extend hp ext,edgeList_extend he ext,vertices_extend hv ext⟩

theorem table_extend {heap : NaturalHeap} {root : ℕ} {xs : List (List Entry)}
    (h : StoredTable heap root xs) (ext : NaturalHeap) : StoredTable (heap++ext) root xs := by
  induction h with
  | nil hp => exact .nil (lookup_extend hp ext)
  | cons hp hr _ ih => exact .cons (lookup_extend hp ext) (row_extend hr ext) ih

def updateTable (es : List (Bits×Bits)) (vs : List Bits) (xs : List (List Entry)) (us : List Bits) :
    List (List Entry) :=
  List.zipWith (fun row u => ResidualRowUpdateProgram.updateRow es u row vs) xs us

def steps (es : List (Bits×Bits)) (vs : List Bits) : List (List Entry) → List Bits → ℕ
  | row::xs,u::us => steps es vs xs us+ResidualRowUpdateProgram.steps es u row vs+19
  | _,_ => 3

private theorem row_slots (pc : Fin 448) (h : ResidualRowUpdateProgram.program pc≠.halt) :
    program (rowLabel pc) = ReferenceProgramLabels.instruction rowLabel (ResidualRowUpdateProgram.program pc) := by
  by_cases hp : pc.val=23
  · have eq : pc=23 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,rowLabel,show ¬32+pc.val<32 by omega,show 32+pc.val≠55 by omega]

private theorem join {s u v : NaturalState 480} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem row_call {heap : NaturalHeap} {r : Registers ℕ} {xs : List Entry}
    {u : Bits} {vs : List Bits} {es : List (Bits×Bits)} (hx : StoredRow heap r.a xs)
    (columns : Vertices heap r.b vs) (hlen : xs.length=vs.length)
    (context : ResidualRowUpdateProgram.Context heap r.c es u)
    (stack : List (Frame ℕ 480)) (tape : Bits) :
    ∃ ext root,StoredRow (heap++ext) root (ResidualRowUpdateProgram.updateRow es u xs vs) ∧
      NaturalRun program (ResidualRowUpdateProgram.steps es u xs vs+3)
        (state heap r stack tape 21) [] (state (heap++ext) (r.set .r3 root) stack tape 22) := by
  obtain ⟨ext,root,rep,body⟩ := ResidualRowUpdateProgram.natural_row hx columns hlen context tape
  let frame : Frame ℕ 480 := ⟨22,.r3,r⟩
  let before := state (heap++ext) (r.set .r3 root) (frame::stack) tape (rowLabel 23)
  have call : tickNatural program (state heap r stack tape 21)=
      some ⟨state heap r (frame::stack) tape (rowLabel 22),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run rowLabel ResidualRowUpdateProgram.program program row_slots body
  have lift := ReferenceProgramStack.run program (frame::stack) lift
  have trace : NaturalRun program (ResidualRowUpdateProgram.steps es u xs vs+1)
      (state heap r (frame::stack) tape (rowLabel 22)) [] before := by
    simpa [before,state,ResidualRowUpdateProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramStack.state] using lift
  have ret : tickNatural program before=some ⟨state (heap++ext) (r.set .r3 root) stack tape 22,[],0⟩ := by
    cases r
    simp [before,frame,state,program,rowLabel,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step call (join trace (.step ret (.done _)))⟩

private theorem head_return {heap : NaturalHeap} {r : Registers ℕ} {xs : List Entry}
    {u : Bits} {vs : List Bits} {es : List (Bits×Bits)} {p q : ℕ} (hx : StoredRow heap r.d xs)
    (context : Context heap r.c es vs) (hp : heap[r.b]?=some (.pair p q)) (hu : BoolList heap p u)
    (hlen : xs.length=vs.length) (caller : Frame ℕ 480) (stack : List (Frame ℕ 480)) (tape : Bits) :
    ∃ ext root,StoredRow (heap++ext) root (ResidualRowUpdateProgram.updateRow es u xs vs) ∧
      NaturalRun program (ResidualRowUpdateProgram.steps es u xs vs+9)
        (state heap r (caller::stack) tape 16) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  obtain ⟨path,columns,hpair,he,hv⟩ := context
  let saved := caller::stack
  let first := r.set .r0 r.d
  let row := first.set .r3 p
  let column := row.set .r1 columns
  let edge := column.set .r2 path
  let pack : Cell ℕ := .pair path p
  let mid := heap++[pack]
  let args := edge.set .r2 heap.length
  have t0 : tickNatural program (state heap r saved tape 16)=
      some ⟨state heap first saved tape 17,[],0⟩ := rfl
  have t1 : tickNatural program (state heap first saved tape 17)=
      some ⟨state heap row saved tape 18,[],0⟩ := by
    simp [first,row,state,program,tickNatural,Registers.get,Registers.set,hp]
  have t2 : tickNatural program (state heap row saved tape 18)=
      some ⟨state heap column saved tape 19,[],0⟩ := by
    simp [first,row,column,state,program,tickNatural,Registers.get,Registers.set,hpair]
  have t3 : tickNatural program (state heap column saved tape 19)=
      some ⟨state heap edge saved tape 20,[],0⟩ := by
    simp [first,row,column,edge,state,program,tickNatural,Registers.get,Registers.set,hpair]
  have alloc : tickNatural program (state heap edge saved tape 20)=some ⟨state mid args saved tape 21,[],0⟩ := by
    simp [first,row,column,edge,args,mid,pack,state,program,tickNatural,Registers.get,
      Registers.set,allocateNatural,Recipe.cell]
  have hctx : ResidualRowUpdateProgram.Context mid args.c es u :=
    ⟨path,p,by simp [mid,args,pack,Registers.set],edgeList_extend he _,boolList_extend hu _⟩
  obtain ⟨ext,root,rep,trace⟩ := row_call (r:=args) (row_extend hx [pack]) (vertices_extend hv [pack])
    hlen hctx saved tape
  let before := state (mid++ext) (args.set .r3 root) saved tape 22
  have ret : tickNatural program before=
      some ⟨state (mid++ext) (caller.saved.set caller.destination root) stack tape caller.continuation,[],0⟩ := by
    simp [before,saved,state,program,tickNatural,Registers.get,Registers.set]
  refine ⟨pack::ext,root,?_,?_⟩
  · simpa only [mid,List.append_assoc,List.singleton_append] using rep
  · have rest := NaturalRun.step alloc (join trace (.step ret (.done _)))
    have run := NaturalRun.step t0 (.step t1 (.step t2 (.step t3 rest)))
    convert run using 1 <;> first | rfl | omega | simp only [mid,List.append_assoc,List.singleton_append]

theorem table_return {heap : NaturalHeap} {r : Registers ℕ} {xs : List (List Entry)}
    {us vs : List Bits} {es : List (Bits×Bits)}
    (input : StoredTable heap r.a xs) (rowLabels : Vertices heap r.b us) (hlen : xs.length=us.length)
    (rectangular : ∀ row ∈ xs,row.length=vs.length)
    (context : Context heap r.c es vs) (caller : Frame ℕ 480) (stack : List (Frame ℕ 480)) (tape : Bits) :
    ∃ ext root,StoredTable (heap++ext) root (updateTable es vs xs us) ∧
      NaturalRun program (steps es vs xs us) (state heap r (caller::stack) tape 0) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction xs generalizing heap r us caller stack with
  | nil =>
    have empty : us=[] := List.length_eq_zero_iff.mp hlen.symm
    subst us
    cases input with
    | nil hp =>
      let saved := caller::stack
      let ext : NaturalHeap := [.nil]
      let fresh := heap.length
      let before := state (heap++ext) (r.set .r3 fresh) saved tape 2
      have branch : tickNatural program (state heap r saved tape 0)=some ⟨state heap r saved tape 1,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,hp]
      have alloc : tickNatural program (state heap r saved tape 1)=some ⟨before,[],0⟩ := by
        simp [ext,fresh,before,state,program,tickNatural,allocateNatural,Recipe.cell]
      have ret : tickNatural program before=some ⟨state (heap++ext)
          (caller.saved.set caller.destination fresh) stack tape caller.continuation,[],0⟩ := by
        simp [before,saved,state,program,tickNatural,Registers.get,Registers.set]
      exact ⟨ext,fresh,.nil (by simp [ext,fresh]),.step branch (.step alloc (.step ret (.done _)))⟩
  | cons x xs ih =>
    cases us with
    | nil => simp at hlen
    | cons u us =>
      have sameLength : xs.length=us.length := Nat.succ.inj hlen
      cases input with
      | @cons _ cell rest _ _ hp hx ht =>
        cases rowLabels with
        | @cons _ word restWords _ _ hl hw hv =>
          let saved := caller::stack
          let first := r.set .r3 cell
          let next := first.set .r0 rest
          let child : Frame ℕ 480 := ⟨7,.r0,next⟩
          let args := next.set .r1 restWords
          let inside : Frame ℕ 480 := ⟨14,.r3,args⟩
          have branch : tickNatural program (state heap r saved tape 0)=
              some ⟨state heap r saved tape 4,[],0⟩ := by
            simp [state,program,tickNatural,Registers.get,tagBranch,hp]
          have readHead : tickNatural program (state heap r saved tape 4)=
              some ⟨state heap first saved tape 5,[],0⟩ := by
            simp [first,state,program,tickNatural,Registers.get,hp]
          have readTail : tickNatural program (state heap first saved tape 5)=
              some ⟨state heap next saved tape 6,[],0⟩ := by
            simp [next,first,state,program,tickNatural,Registers.get,Registers.set,hp]
          have callTail : tickNatural program (state heap next saved tape 6)=
              some ⟨state heap next (child::saved) tape 12,[],0⟩ := rfl
          have wordTail : tickNatural program (state heap next (child::saved) tape 12)=
              some ⟨state heap args (child::saved) tape 13,[],0⟩ := by
            simp [args,next,first,state,program,tickNatural,Registers.get,Registers.set,hl]
          have descend : tickNatural program (state heap args (child::saved) tape 13)=
              some ⟨state heap args (inside::child::saved) tape 0,[],0⟩ := rfl
          obtain ⟨et,tail,hout,tailRun⟩ := ih (r:=args) ht hv sameLength
            (fun row h => rectangular row (List.mem_cons_of_mem _ h)) context inside (child::saved)
          let mid := heap++et
          let returned := next.set .r0 tail
          let headFrame : Frame ℕ 480 := ⟨8,.r3,returned⟩
          have yieldTail : tickNatural program (state mid (args.set .r3 tail) (child::saved) tape 14)=
              some ⟨state mid returned saved tape 7,[],0⟩ := by
            simp [args,child,returned,state,program,tickNatural,Registers.get,Registers.set]
          have callHead : tickNatural program (state mid returned saved tape 7)=
              some ⟨state mid returned (headFrame::saved) tape 16,[],0⟩ := rfl
          obtain ⟨eh,head,hhead,headRun⟩ := head_return (r:=returned) (row_extend hx et)
            (context_extend context et) (lookup_extend hl et) (boolList_extend hw et)
            (rectangular x List.mem_cons_self) headFrame saved tape
          let grown := mid++eh
          let fresh := grown.length
          let pair : Cell ℕ := .pair head tail
          let out := grown++[pair]
          let afterHead := returned.set .r3 head
          let before := state out (afterHead.set .r3 fresh) saved tape 2
          have alloc : tickNatural program (state grown afterHead saved tape 8)=some ⟨before,[],0⟩ := by
            simp [before,out,fresh,pair,afterHead,returned,state,program,tickNatural,Registers.get,
              Registers.set,allocateNatural,Recipe.cell]
          have ret : tickNatural program before=some ⟨state out (caller.saved.set caller.destination fresh)
              stack tape caller.continuation,[],0⟩ := by
            simp [before,afterHead,saved,state,program,tickNatural,Registers.get,Registers.set]
          have result : StoredTable out fresh (updateTable es vs (x::xs) (u::us)) :=
            .cons (by simp [out,fresh,pair]) (row_extend hhead [pair])
              (table_extend (table_extend hout eh) [pair])
          refine ⟨et++eh++[pair],fresh,?_,?_⟩
          · simpa only [out,grown,mid,List.append_assoc] using result
          · have finish := NaturalRun.step alloc (.step ret (.done _))
            have headTrace := NaturalRun.step yieldTail (.step callHead (join headRun finish))
            have tailTrace := NaturalRun.step callTail (.step wordTail (.step descend (join tailRun headTrace)))
            have trace := NaturalRun.step branch (.step readHead (.step readTail tailTrace))
            simp only [steps]
            convert trace using 1 <;> first | rfl | omega | simp only [out,grown,mid,List.append_assoc]

theorem natural_table {heap : NaturalHeap} {r : Registers ℕ} {xs : List (List Entry)}
    {us vs : List Bits} {es : List (Bits×Bits)}
    (input : StoredTable heap r.a xs) (rowLabels : Vertices heap r.b us) (hlen : xs.length=us.length)
    (rectangular : ∀ row ∈ xs,row.length=vs.length) (context : Context heap r.c es vs) (tape : Bits) :
    ∃ ext root,StoredTable (heap++ext) root (updateTable es vs xs us) ∧
      NaturalRun program (steps es vs xs us+1) (state heap r [] tape 26) []
        (state (heap++ext) (r.set .r3 root) [] tape 27) := by
  let frame : Frame ℕ 480 := ⟨27,.r3,r⟩
  obtain ⟨ext,root,hrep,hrun⟩ := table_return input rowLabels hlen rectangular context frame [] tape
  have call : tickNatural program (state heap r [] tape 26)=some ⟨state heap r [frame] tape 0,[],0⟩ := rfl
  exact ⟨ext,root,hrep,.step call hrun⟩

private theorem row_invariant (es : List (Bits×Bits)) (u : Bits) (xs : List Entry) (vs : List Bits) (B : ℕ)
    (h : ∀ e ∈ xs,Canonical e.1 ∧ e.2.length≤B) :
    ∀ e ∈ ResidualRowUpdateProgram.updateRow es u xs vs,Canonical e.1 ∧ e.2.length≤B := by
  induction xs generalizing vs with
  | nil => simp [ResidualRowUpdateProgram.updateRow]
  | cons x xs ih =>
    cases vs with
    | nil => simp [ResidualRowUpdateProgram.updateRow]
    | cons v vs =>
      intro e he
      simp only [ResidualRowUpdateProgram.updateRow,List.zipWith_cons_cons,List.mem_cons] at he
      rcases he with rfl | he
      · have first := h x List.mem_cons_self
        exact ⟨(ResidualCellUpdateProgram.updated_spec es u v x.1 first.1).1,first.2⟩
      · exact ih vs (fun y hy => h y (List.mem_cons_of_mem _ hy)) e he

theorem invariant (es : List (Bits×Bits)) (vs : List Bits) (xs : List (List Entry)) (us : List Bits) (B : ℕ)
    (h : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B) :
    ∀ row ∈ updateTable es vs xs us,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B := by
  induction xs generalizing us with
  | nil => simp [updateTable]
  | cons row xs ih =>
    cases us with
    | nil => simp [updateTable]
    | cons u us =>
      intro out hr
      simp only [updateTable,List.zipWith_cons_cons,List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact row_invariant es u row vs B (h row List.mem_cons_self)
      · exact ih us (fun next hn => h next (List.mem_cons_of_mem _ hn)) out hr

def instructionBound (m d q W B : ℕ) : ℕ :=
  m*(ResidualRowUpdateProgram.instructionBound d q W B+19)+4

theorem steps_le (es : List (Bits×Bits)) (vs : List Bits) (xs : List (List Entry)) (us : List Bits)
    (W B : ℕ) (hu : ∀ u ∈ us,u.length≤W) (hv : ∀ v ∈ vs,v.length≤W)
    (width : ∀ row ∈ xs,row.length=vs.length ∧ ∀ e ∈ row,Canonical e.1 ∧ e.1.magnitude.length≤B)
    (edges : ∀ e ∈ es,SupportRecoveryProgram.EdgeWidths W e) :
    steps es vs xs us+1 ≤ instructionBound xs.length vs.length es.length W B := by
  induction xs generalizing us with
  | nil => simp [steps,instructionBound]
  | cons row xs ih =>
    cases us with
    | nil => simp [steps,instructionBound]
    | cons u us =>
      obtain ⟨hlen,hw⟩ := width row List.mem_cons_self
      have first := ResidualRowUpdateProgram.steps_le es u row vs W B (hu u List.mem_cons_self) hv hw edges
      rw [hlen] at first
      have tail := ih us (fun v h => hu v (List.mem_cons_of_mem _ h))
        (fun x h => width x (List.mem_cons_of_mem _ h))
      simp only [steps,instructionBound,List.length_cons,Nat.add_mul,Nat.one_mul] at tail ⊢
      omega

open IntegralNetworkFlow IntegralNetworkFlow.Tabulated SupportSearchEncoding

variable {n : ℕ} {s t : Fin n} {c : Capacity (Fin n)}

theorem table_matches (f : Flow c s t) (p : SimplePath f.residual s t)
    (xs : List (List Entry)) (us vs : List (Fin n)) (values : ValueTable f xs us vs)
    (canonical : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) :
    ValueTable (f.augment p)
      (updateTable ((FlowTable.edgeList p).map (encodeEdge label)) (vs.map label) xs (us.map label)) us vs := by
  induction values with
  | nil => exact .nil
  | @cons row u xs us h _ ih =>
    exact .cons (ResidualRowUpdateProgram.row_matches f p u row vs h (canonical row List.mem_cons_self) label hlabel)
      (ih (fun x hx => canonical x (List.mem_cons_of_mem _ hx)))

private theorem at_entry (s : NaturalState 480) (hp : s.pc=26) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 26 := by
  cases s
  simp_all [state]

theorem physical_augment {H A W B : ℕ} (f : Flow c s t) (p : SimplePath f.residual s t)
    (xs : List (List Entry)) (us vs : List (Fin n)) (values : ValueTable f xs us vs)
    (fields : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B)
    (capacities : ∀ u v,(max (c u v) (c v u)).size≤B)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (labels : ∀ i,(label i).length≤W)
    (initial : BitState 480) (bounded : initial.Bounded H A) (hp : initial.pc=26) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : StoredTable (eraseState initial).heap (eraseState initial).registers.a xs)
    (rows : Vertices (eraseState initial).heap (eraseState initial).registers.b (us.map label))
    (context : Context (eraseState initial).heap (eraseState initial).registers.c
      ((FlowTable.edgeList p).map (encodeEdge label)) (vs.map label)) :
    let es := (FlowTable.edgeList p).map (encodeEdge label)
    let ys := updateTable es (vs.map label) xs (us.map label)
    ∃ charge out,Run program (steps es (vs.map label) xs (us.map label)+1) charge initial [] out ∧
      StoredTable (eraseState out).heap (eraseState out).registers.d ys ∧
      ValueTable (f.augment p) ys us vs ∧ (∀ row ∈ ys,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=27 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 480 H A (instructionBound us.length vs.length n W B) := by
  let old := eraseState initial
  let es := (FlowTable.edgeList p).map (encodeEdge label)
  let left := us.map label
  let right := vs.map label
  have rect (row : List Entry) (hrow : row ∈ xs) : row.length=right.length ∧
      ∀ e ∈ row,Canonical e.1 ∧ e.1.magnitude.length≤B := by
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hrow
    have hu : i < us.length := by rwa [← values.length_eq]
    have rel := values.get hi hu
    refine ⟨by simpa only [right,List.length_map,List.get_eq_getElem] using rel.length_eq,?_⟩
    intro e he
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp he
    have hv : j < vs.length := by rwa [← rel.length_eq]
    have slot := rel.get hj hv
    have norm := (fields _ hrow _ he).1
    exact ⟨norm,(ResidualCapacityProgram.amount_width f us[i] vs[j] _ slot.1 norm).trans (capacities _ _)⟩
  have hrows : xs.length=left.length := by simpa only [left,List.length_map] using values.length_eq
  obtain ⟨ext,root,hrep,body⟩ := natural_table input rows hrows (fun row h => (rect row h).1) context old.source
  let final := state (old.heap++ext) (old.registers.set .r3 root) [] old.source 27
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have trace : NaturalRun program (steps es right xs left+1) old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have stop : tickNatural program final=none := rfl
  obtain ⟨charge,out,hr,hout,hstop,hcharge,htape⟩ := terminating_simulation bounded trace stop
  refine ⟨charge,out,hr,?_,table_matches f p xs us vs values (fun row h e he => (fields row h e he).1) label hlabel,
    invariant es right xs left B fields,htape,?_,?_,⟨ext,?_⟩,hstop,hcharge.trans ?_⟩
  · rw [hout]; exact hrep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl
  · have names (vs : List (Fin n)) : ∀ u ∈ vs.map label,u.length≤W := by
      intro u hu
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
      exact labels i
    have ew : ∀ e ∈ es,SupportRecoveryProgram.EdgeWidths W e := by
      intro e he
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp he
      exact ⟨labels a.1,labels a.2⟩
    have count : es.length≤n := by
      simpa only [es,List.length_map,FlowTable.edgeList_length,Fintype.card_fin] using p.edgeLength_lt_card.le
    have k := steps_le es right xs left W B (names us) (names vs) rect ew
    simp only [right,List.length_map,values.length_eq] at k
    refine complete_mono 480 H A _ _ (k.trans ?_)
    unfold instructionBound ResidualRowUpdateProgram.instructionBound ResidualCellUpdateProgram.instructionBound
    gcongr

end DirectedFlowCutGap.ResidualTableUpdateProgram
