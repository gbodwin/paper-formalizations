import DirectedFlowCutGap.ResidualCellUpdateProgram

/-!
# Updating one represented flow row

The row scan traverses the flow cells and column labels together. It uses
the same stored row label and residual path at every cell, then returns
the updated row in the residual matrix reader's existing layout.
-/

namespace DirectedFlowCutGap.ResidualRowUpdateProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor GraphWalkExtension
open ResidualRowProgram (Entry StoredEntry StoredRow entry_extend)
open GraphDiscoveryProgram (Vertices vertices_extend)
open BinarySigned (Canonical decode)

def cellLabel (pc : Fin 424) : Fin 448 := ⟨24+pc.val,by omega⟩

def program : Program 448 := fun pc =>
  if pc.val<24 then
    match pc.val with
    | 0 => .branch .r0 1 23 23 4
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
    | 18 => .field .r1 .r2 false 19
    | 19 => .field .r2 .r2 true 20
    | 20 => .call (cellLabel 30) 21 .r3
    | 21 => .ret .r3
    | 22 => .call 0 23 .r3
    | _ => .halt
  else if pc.val=55 then .ret .r3
  else ReferenceProgramLabels.instruction cellLabel
    (ResidualCellUpdateProgram.program ⟨pc.val-24,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 448))
    (tape : Bits) (pc : Fin 448) : NaturalState 448 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def Context (heap : NaturalHeap) (root : ℕ) (es : List (Bits×Bits)) (u : Bits) : Prop :=
  ∃ path label,heap[root]?=some (.pair path label) ∧ EdgeList heap path es ∧ BoolList heap label u

theorem context_extend {heap : NaturalHeap} {root : ℕ} {es : List (Bits×Bits)} {u : Bits}
    (h : Context heap root es u) (ext : NaturalHeap) : Context (heap++ext) root es u := by
  obtain ⟨path,label,hp,he,hu⟩ := h
  exact ⟨path,label,lookup_extend hp ext,edgeList_extend he ext,boolList_extend hu ext⟩

def updateRow (es : List (Bits×Bits)) (u : Bits) (xs : List Entry) (vs : List Bits) : List Entry :=
  List.zipWith (fun x v => (ResidualCellUpdateProgram.updated es u v x.1,x.2)) xs vs

def steps (es : List (Bits×Bits)) (u : Bits) : List Entry → List Bits → ℕ
  | x::xs,v::vs => steps es u xs vs+ResidualCellUpdateProgram.steps es u v x.1+17
  | _,_ => 3

private theorem cell_slots (pc : Fin 424) (h : ResidualCellUpdateProgram.program pc≠.halt) :
    program (cellLabel pc) = ReferenceProgramLabels.instruction cellLabel (ResidualCellUpdateProgram.program pc) := by
  by_cases hp : pc.val=31
  · have eq : pc=31 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,cellLabel,show ¬24+pc.val<24 by omega,show 24+pc.val≠55 by omega]

private theorem join {s u v : NaturalState 448} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem cell_call {heap : NaturalHeap} {r : Registers ℕ} {x : Entry}
    {u v : Bits} {es : List (Bits×Bits)} (hx : StoredEntry heap r.a x)
    (he : EdgeList heap r.b es) (hu : BoolList heap r.c u) (hv : BoolList heap r.d v)
    (stack : List (Frame ℕ 448)) (tape : Bits) :
    ∃ ext root,StoredEntry (heap++ext) root (ResidualCellUpdateProgram.updated es u v x.1,x.2) ∧
      NaturalRun program (ResidualCellUpdateProgram.steps es u v x.1+2)
        (state heap r stack tape 20) [] (state (heap++ext) (r.set .r3 root) stack tape 21) := by
  obtain ⟨ext,root,rep,body⟩ := ResidualCellUpdateProgram.natural_update hx he hu hv tape
  let frame : Frame ℕ 448 := ⟨21,.r3,r⟩
  let before := state (heap++ext) (r.set .r3 root) (frame::stack) tape (cellLabel 31)
  have call : tickNatural program (state heap r stack tape 20)=
      some ⟨state heap r (frame::stack) tape (cellLabel 30),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run cellLabel ResidualCellUpdateProgram.program program cell_slots body
  have lift := ReferenceProgramStack.run program (frame::stack) lift
  have trace : NaturalRun program (ResidualCellUpdateProgram.steps es u v x.1)
      (state heap r (frame::stack) tape (cellLabel 30)) [] before := by
    simpa [before,state,ResidualCellUpdateProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramStack.state] using lift
  have ret : tickNatural program before=some ⟨state (heap++ext) (r.set .r3 root) stack tape 21,[],0⟩ := by
    cases r
    simp [before,frame,state,program,cellLabel,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step call (join trace (.step ret (.done _)))⟩

private theorem head_return {heap : NaturalHeap} {r : Registers ℕ} {x : Entry}
    {u v : Bits} {es : List (Bits×Bits)} {p q : ℕ} (hx : StoredEntry heap r.d x)
    (hc : Context heap r.c es u) (hp : heap[r.b]?=some (.pair p q)) (hv : BoolList heap p v)
    (caller : Frame ℕ 448) (stack : List (Frame ℕ 448)) (tape : Bits) :
    ∃ ext root,StoredEntry (heap++ext) root (ResidualCellUpdateProgram.updated es u v x.1,x.2) ∧
      NaturalRun program (ResidualCellUpdateProgram.steps es u v x.1+7)
        (state heap r (caller::stack) tape 16) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  obtain ⟨path,row,hpair,he,hu⟩ := hc
  let saved := caller::stack
  let first := r.set .r0 r.d
  let column := first.set .r3 p
  let edge := column.set .r1 path
  let args := edge.set .r2 row
  have t0 : tickNatural program (state heap r saved tape 16)=
      some ⟨state heap first saved tape 17,[],0⟩ := rfl
  have t1 : tickNatural program (state heap first saved tape 17)=
      some ⟨state heap column saved tape 18,[],0⟩ := by
    simp [first,column,state,program,tickNatural,Registers.get,Registers.set,hp]
  have t2 : tickNatural program (state heap column saved tape 18)=
      some ⟨state heap edge saved tape 19,[],0⟩ := by
    simp [first,column,edge,state,program,tickNatural,Registers.get,Registers.set,hpair]
  have t3 : tickNatural program (state heap edge saved tape 19)=
      some ⟨state heap args saved tape 20,[],0⟩ := by
    simp [first,column,edge,args,state,program,tickNatural,Registers.get,Registers.set,hpair]
  obtain ⟨ext,root,rep,trace⟩ := cell_call (r:=args) hx he hu hv saved tape
  let before := state (heap++ext) (args.set .r3 root) saved tape 21
  have ret : tickNatural program before=
      some ⟨state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation,[],0⟩ := by
    simp [before,saved,state,program,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step t0 (.step t1 (.step t2 (.step t3 (join trace (.step ret (.done _))))))⟩

theorem row_return {heap : NaturalHeap} {r : Registers ℕ} {xs : List Entry}
    {u : Bits} {vs : List Bits} {es : List (Bits×Bits)}
    (input : StoredRow heap r.a xs) (columns : Vertices heap r.b vs) (hlen : xs.length=vs.length)
    (context : Context heap r.c es u) (caller : Frame ℕ 448) (stack : List (Frame ℕ 448)) (tape : Bits) :
    ∃ ext root,StoredRow (heap++ext) root (updateRow es u xs vs) ∧
      NaturalRun program (steps es u xs vs) (state heap r (caller::stack) tape 0) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction xs generalizing heap r vs caller stack with
  | nil =>
    have empty : vs=[] := List.length_eq_zero_iff.mp hlen.symm
    subst vs
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
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      have sameLength : xs.length=vs.length := Nat.succ.inj hlen
      cases input with
      | @cons _ cell rest _ _ hp hx ht =>
        cases columns with
        | @cons _ word restWords _ _ hl hw hv =>
          let saved := caller::stack
          let first := r.set .r3 cell
          let next := first.set .r0 rest
          let child : Frame ℕ 448 := ⟨7,.r0,next⟩
          let args := next.set .r1 restWords
          let inside : Frame ℕ 448 := ⟨14,.r3,args⟩
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
          obtain ⟨et,tail,hout,tailRun⟩ := ih (r:=args) ht hv sameLength context inside (child::saved)
          let mid := heap++et
          let returned := next.set .r0 tail
          let headFrame : Frame ℕ 448 := ⟨8,.r3,returned⟩
          have yieldTail : tickNatural program (state mid (args.set .r3 tail) (child::saved) tape 14)=
              some ⟨state mid returned saved tape 7,[],0⟩ := by
            simp [args,child,returned,state,program,tickNatural,Registers.get,Registers.set]
          have callHead : tickNatural program (state mid returned saved tape 7)=
              some ⟨state mid returned (headFrame::saved) tape 16,[],0⟩ := rfl
          obtain ⟨eh,head,hhead,headRun⟩ := head_return (r:=returned) (entry_extend hx et)
            (context_extend context et) (lookup_extend hl et) (boolList_extend hw et) headFrame saved tape
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
          have result : StoredRow out fresh (updateRow es u (x::xs) (v::vs)) :=
            .cons (by simp [out,fresh,pair]) (entry_extend hhead [pair])
              (ResidualRowProgram.row_extend (ResidualRowProgram.row_extend hout eh) [pair])
          refine ⟨et++eh++[pair],fresh,?_,?_⟩
          · simpa only [out,grown,mid,List.append_assoc] using result
          · have finish := NaturalRun.step alloc (.step ret (.done _))
            have headTrace := NaturalRun.step yieldTail (.step callHead (join headRun finish))
            have tailTrace := NaturalRun.step callTail (.step wordTail (.step descend (join tailRun headTrace)))
            have trace := NaturalRun.step branch (.step readHead (.step readTail tailTrace))
            simp only [steps]
            convert trace using 1 <;> first | rfl | omega | simp only [out,grown,mid,List.append_assoc]

theorem natural_row {heap : NaturalHeap} {r : Registers ℕ} {xs : List Entry}
    {u : Bits} {vs : List Bits} {es : List (Bits×Bits)}
    (input : StoredRow heap r.a xs) (columns : Vertices heap r.b vs) (hlen : xs.length=vs.length)
    (context : Context heap r.c es u) (tape : Bits) :
    ∃ ext root,StoredRow (heap++ext) root (updateRow es u xs vs) ∧
      NaturalRun program (steps es u xs vs+1) (state heap r [] tape 22) []
        (state (heap++ext) (r.set .r3 root) [] tape 23) := by
  let frame : Frame ℕ 448 := ⟨23,.r3,r⟩
  obtain ⟨ext,root,hrep,hrun⟩ := row_return input columns hlen context frame [] tape
  have call : tickNatural program (state heap r [] tape 22)=some ⟨state heap r [frame] tape 0,[],0⟩ := rfl
  exact ⟨ext,root,hrep,.step call hrun⟩

def instructionBound (m q W B : ℕ) : ℕ := m*(ResidualCellUpdateProgram.instructionBound q W B+17)+4

theorem steps_le (es : List (Bits×Bits)) (u : Bits) (xs : List Entry) (vs : List Bits)
    (W B : ℕ) (hu : u.length≤W) (hv : ∀ v ∈ vs,v.length≤W)
    (width : ∀ x ∈ xs,Canonical x.1 ∧ x.1.magnitude.length≤B)
    (edges : ∀ e ∈ es,SupportRecoveryProgram.EdgeWidths W e) :
    steps es u xs vs+1 ≤ instructionBound xs.length es.length W B := by
  induction xs generalizing vs with
  | nil => simp [steps,instructionBound]
  | cons x xs ih =>
    cases vs with
    | nil => simp [steps,instructionBound]
    | cons v vs =>
      obtain ⟨canon,hw⟩ := width x List.mem_cons_self
      have first := ResidualCellUpdateProgram.steps_le es u v x.1 canon W B hu (hv v List.mem_cons_self) hw edges
      have tail := ih vs (fun y hy => hv y (List.mem_cons_of_mem _ hy))
        (fun y hy => width y (List.mem_cons_of_mem _ hy))
      simp only [steps,instructionBound,List.length_cons,Nat.add_mul,Nat.one_mul] at tail ⊢
      omega

open IntegralNetworkFlow IntegralNetworkFlow.Tabulated SupportSearchEncoding

theorem row_matches {n : ℕ} {s t : Fin n} {c : Capacity (Fin n)} (f : Flow c s t)
    (p : SimplePath f.residual s t) (u : Fin n) (xs : List Entry) (vs : List (Fin n))
    (values : List.Forall₂ (fun x v => decode x.1=f.amount u v ∧ value x.2=c u v) xs vs)
    (canonical : ∀ x ∈ xs,Canonical x.1) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) :
    List.Forall₂ (fun x v => decode x.1=(f.augment p).amount u v ∧ value x.2=c u v)
      (updateRow ((FlowTable.edgeList p).map (encodeEdge label)) (label u) xs (vs.map label)) vs := by
  induction values with
  | nil => exact .nil
  | @cons x v xs vs h _ ih =>
    exact .cons ⟨ResidualCellUpdateProgram.update_matches_augment f p u v label hlabel
      x.1 (canonical x List.mem_cons_self) h.1,h.2⟩
      (ih (fun y hy => canonical y (List.mem_cons_of_mem _ hy)))

end DirectedFlowCutGap.ResidualRowUpdateProgram
