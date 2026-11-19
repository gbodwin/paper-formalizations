import DirectedFlowCutGap.ResidualRowProgram
import DirectedFlowCutGap.GraphAdjacencyProgram
import DirectedFlowCutGap.PathCostMaterialization

/-!
# Physical residual adjacency matrix

The program scans retained rows of flow amounts and capacities and calls
the residual tester on every entry. The output uses the same Boolean
matrix layout as the fixed graph-search program.
-/

namespace DirectedFlowCutGap.ResidualMatrixProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor IntegralNetworkFlow
open BinarySigned (Canonical decode)
open ResidualRowProgram (Entry StoredRow)
open PathCostMaterialization (WordList)
open BinaryPointerListRead (PointerList)

inductive StoredTable (heap : NaturalHeap) : ℕ → List (List Entry) → Prop
  | nil {p : ℕ} : heap[p]?=some .nil → StoredTable heap p []
  | cons {p head tail : ℕ} {row : List Entry} {rows : List (List Entry)} :
      heap[p]?=some (.pair head tail) → StoredRow heap head row → StoredTable heap tail rows →
        StoredTable heap p (row::rows)

def rowLabel (pc : Fin 76) : Fin 92 := ⟨16+pc.val,by omega⟩

def program : Program 92 := fun pc =>
  if pc.val < 16 then
    match pc.val with
    | 0 => .branch .r0 1 15 15 4
    | 1 => .make .r3 .nil 2
    | 2 => .ret .r3
    | 4 => .field .r2 .r0 false 5
    | 5 => .field .r0 .r0 true 6
    | 6 => .call 0 7 .r1
    | 7 => .call 10 8 .r3
    | 8 => .make .r3 (.pair .r3 .r1) 2
    | 10 => .move .r0 .r2 11
    | 11 => .call (rowLabel 14) 12 .r3
    | 12 => .ret .r3
    | 14 => .call 0 15 .r3
    | _ => .halt
  else if pc.val=31 then .ret .r3
  else ReferenceProgramLabels.instruction rowLabel (ResidualRowProgram.program ⟨pc.val-16,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 92)) (tape : Bits)
    (pc : Fin 92) : NaturalState 92 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def flags (xs : List (List Entry)) : List Bits := xs.map (List.map ResidualRowProgram.flag)

def steps : List (List Entry) → ℕ
  | [] => 3
  | x::xs => steps xs+ResidualRowProgram.steps x+12

private theorem row_slots (pc : Fin 76) (h : ResidualRowProgram.program pc≠.halt) :
    program (rowLabel pc) = ReferenceProgramLabels.instruction rowLabel (ResidualRowProgram.program pc) := by
  by_cases hp : pc.val=15
  · have eq : pc=15 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,rowLabel,show ¬16+pc.val<16 by omega,show 16+pc.val≠31 by omega]

private theorem join {s u v : NaturalState 92} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem read_row {heap : NaturalHeap} {r : Registers ℕ} {x : List Entry}
    (row : StoredRow heap r.c x) (canonical : ∀ e ∈ x,Canonical e.1)
    (caller : Frame ℕ 92) (stack : List (Frame ℕ 92)) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (x.map ResidualRowProgram.flag) ∧
      NaturalRun program (ResidualRowProgram.steps x+5)
        (state heap r (caller::stack) tape 10) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  let saved := caller::stack
  let args := r.set .r0 r.c
  let frame : Frame ℕ 92 := ⟨12,.r3,args⟩
  have input : StoredRow heap args.a x := by cases r; exact row
  obtain ⟨ext,root,hrep,hrun⟩ := ResidualRowProgram.natural_row input canonical tape
  have move : tickNatural program (state heap r saved tape 10)=some ⟨state heap args saved tape 11,[],0⟩ := rfl
  have call : tickNatural program (state heap args saved tape 11)=
      some ⟨state heap args (frame::saved) tape (rowLabel 14),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run rowLabel ResidualRowProgram.program program row_slots hrun
  have lift := ReferenceProgramStack.run program (frame::saved) lift
  let mid := heap++ext
  let before := state mid (args.set .r3 root) (frame::saved) tape (rowLabel 15)
  let after := state mid (args.set .r3 root) saved tape 12
  let final := state mid (caller.saved.set caller.destination root) stack tape caller.continuation
  have body : NaturalRun program (ResidualRowProgram.steps x+1)
      (state heap args (frame::saved) tape (rowLabel 14)) [] before := by
    simpa [before,state,mid,ResidualRowProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program before=some ⟨after,[],0⟩ := by
    cases r
    simp [before,after,args,frame,state,program,rowLabel,tickNatural,Registers.get,Registers.set]
  have endCall : tickNatural program after=some ⟨final,[],0⟩ := by
    cases r
    simp [after,final,args,saved,state,program,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,hrep,.step move (.step call (join body (.step ret (.step endCall (.done final)))))⟩

theorem table_return {heap : NaturalHeap} {r : Registers ℕ} {xs : List (List Entry)}
    (input : StoredTable heap r.a xs) (canonical : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1)
    (caller : Frame ℕ 92) (stack : List (Frame ℕ 92)) (tape : Bits) :
    ∃ ext root,WordList (heap++ext) root (flags xs) ∧
      NaturalRun program (steps xs) (state heap r (caller::stack) tape 0) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction xs generalizing heap r caller stack with
  | nil =>
    cases input with
    | nil hp =>
      let saved := caller::stack
      let empty := heap.length
      let ext : NaturalHeap := [.nil]
      let before := state (heap++ext) (r.set .r3 empty) saved tape 2
      have branch : tickNatural program (state heap r saved tape 0)=some ⟨state heap r saved tape 1,[],0⟩ := by
        simp [state,tickNatural,program,Registers.get,tagBranch,hp]
      have alloc : tickNatural program (state heap r saved tape 1)=some ⟨before,[],0⟩ := by
        simp [before,empty,ext,state,tickNatural,program,allocateNatural,Recipe.cell]
      have ret : tickNatural program before=
          some ⟨state (heap++ext) (caller.saved.set caller.destination empty) stack tape caller.continuation,[],0⟩ := by
        cases r
        simp [before,saved,state,tickNatural,program,Registers.get,Registers.set]
      exact ⟨ext,empty,.nil (by simp [ext,empty]),.step branch (.step alloc (.step ret (.done _)))⟩
  | cons x xs ih =>
    cases input with
    | @cons _ head tail _ _ hp hx ht =>
      let saved := caller::stack
      let first := r.set .r2 head
      let args := first.set .r0 tail
      let ftail : Frame ℕ 92 := ⟨7,.r1,args⟩
      have branch : tickNatural program (state heap r saved tape 0)=
          some ⟨state heap r saved tape 4,[],0⟩ := by
        simp [state,tickNatural,program,Registers.get,tagBranch,hp]
      have readHead : tickNatural program (state heap r saved tape 4)=
          some ⟨state heap first saved tape 5,[],0⟩ := by
        simp [first,state,tickNatural,program,Registers.get,hp]
      have readTail : tickNatural program (state heap first saved tape 5)=
          some ⟨state heap args saved tape 6,[],0⟩ := by
        cases r
        simp [args,first,state,tickNatural,program,Registers.get,Registers.set,hp]
      have callTail : tickNatural program (state heap args saved tape 6)=
          some ⟨state heap args (ftail::saved) tape 0,[],0⟩ := rfl
      have inputTail : StoredTable heap args.a xs := by cases r; exact ht
      obtain ⟨et,rest,hrest,hrun⟩ := ih inputTail
        (fun row hrow => canonical row (List.mem_cons_of_mem _ hrow)) ftail saved
      let mid := heap++et
      let headArgs := args.set .r1 rest
      let fhead : Frame ℕ 92 := ⟨8,.r3,headArgs⟩
      have headInput : StoredRow mid headArgs.c x := by cases r; exact ResidualRowProgram.row_extend hx et
      have callHead : tickNatural program (state mid headArgs saved tape 7)=
          some ⟨state mid headArgs (fhead::saved) tape 10,[],0⟩ := rfl
      obtain ⟨eh,row,hrow,hhead⟩ := read_row headInput (canonical x List.mem_cons_self) fhead saved tape
      let grown := mid++eh
      let cell : Cell ℕ := .pair row rest
      let fresh := grown.length
      let out := grown++[cell]
      let returned := headArgs.set .r3 row
      let before := state out (returned.set .r3 fresh) saved tape 2
      have alloc : tickNatural program (state grown returned saved tape 8)=some ⟨before,[],0⟩ := by
        cases r
        simp [before,out,cell,fresh,returned,headArgs,args,first,state,tickNatural,program,
          Registers.get,Registers.set,allocateNatural,Recipe.cell]
      have ret : tickNatural program before=some ⟨state out (caller.saved.set caller.destination fresh)
          stack tape caller.continuation,[],0⟩ := by
        cases r
        simp [before,returned,headArgs,args,first,saved,state,tickNatural,program,Registers.get,Registers.set]
      have result : WordList out fresh (flags (x::xs)) := .cons (by simp [out,fresh,cell])
        (boolList_extend hrow [cell]) (PathCostMaterialization.list_extend (PathCostMaterialization.list_extend hrest eh) [cell])
      refine ⟨et++eh++[cell],fresh,?_,?_⟩
      · simpa only [out,grown,mid,List.append_assoc] using result
      · have trace := NaturalRun.step branch (.step readHead (.step readTail (.step callTail
          (join hrun (.step callHead (join hhead (.step alloc (.step ret (.done _)))))))))
        simp only [steps]
        convert trace using 1 <;> first | rfl | omega | simp only [out,grown,mid,List.append_assoc]

theorem matrix_of_wordList {heap : NaturalHeap} {root : ℕ} {rows : List Bits} (input : WordList heap root rows) :
    GraphAdjacencyProgram.Matrix heap root rows := by
  induction input with
  | nil hp =>
    refine ⟨[],rfl,.nil hp,?_⟩
    simp
  | @cons root head tail x xs hp hx _ ih =>
    obtain ⟨roots,hlen,rest,stored⟩ := ih
    refine ⟨head::roots,by simp [hlen],.cons hp rest,?_⟩
    intro i hi
    cases i with
    | zero => exact hx
    | succ i => exact stored i (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi)

theorem natural_matrix {heap : NaturalHeap} {r : Registers ℕ} {xs : List (List Entry)}
    (input : StoredTable heap r.a xs) (canonical : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1) (tape : Bits) :
    ∃ ext root,GraphAdjacencyProgram.Matrix (heap++ext) root (flags xs) ∧
      NaturalRun program (steps xs+1) (state heap r [] tape 14) []
        (state (heap++ext) (r.set .r3 root) [] tape 15) := by
  let frame : Frame ℕ 92 := ⟨15,.r3,r⟩
  obtain ⟨ext,root,hrep,hrun⟩ := table_return input canonical frame [] tape
  have call : tickNatural program (state heap r [] tape 14)=some ⟨state heap r [frame] tape 0,[],0⟩ := rfl
  exact ⟨ext,root,matrix_of_wordList hrep,.step call hrun⟩

def instructionBound (n m W : ℕ) : ℕ :=
  n*(ResidualRowProgram.instructionBound m W+12)+4

theorem steps_le (xs : List (List Entry)) (m W : ℕ)
    (width : ∀ row ∈ xs,row.length=m ∧ ∀ e ∈ row,e.1.magnitude.length ≤ W ∧ e.2.length ≤ W) :
    steps xs+1 ≤ instructionBound xs.length m W := by
  have bound : steps xs ≤ xs.length*(ResidualRowProgram.instructionBound m W+12)+3 := by
    induction xs with
    | nil => simp [steps]
    | cons row rows ih =>
      obtain ⟨hlen,hw⟩ := width row List.mem_cons_self
      have first := ResidualRowProgram.steps_le row W hw
      rw [hlen] at first
      have tail := ih (fun r hr => width r (List.mem_cons_of_mem _ hr))
      simp only [steps,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  exact Nat.add_le_add_right bound 1

variable {V : Type} [Fintype V] {c : Capacity V} {s t : V}

def ValueTable (f : Flow c s t) (xs : List (List Entry)) (us vs : List V) : Prop :=
  List.Forall₂ (fun row u => List.Forall₂ (fun e v => decode e.1=f.amount u v ∧ value e.2=c u v)
    row vs) xs us

def residualFlags (f : Flow c s t) (us vs : List V) : List Bits :=
  us.map (fun u => vs.map (fun v => decide (f.amount u v < (c u v : ℤ))))

theorem flags_eq (f : Flow c s t) {xs : List (List Entry)} {us vs : List V}
    (values : ValueTable f xs us vs) : flags xs=residualFlags f us vs := by
  induction values with
  | nil => rfl
  | @cons row u rows us h _ ih =>
    simp only [flags,residualFlags,List.map_cons]
    exact congrArg₂ List.cons (ResidualRowProgram.row_matches f u row vs h) ih

private theorem at_entry (s : NaturalState 92) (hp : s.pc=14) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 14 := by
  cases s
  simp_all [state]

theorem physical_matrix {H A W : ℕ} (f : Flow c s t) (xs : List (List Entry)) (us vs : List V)
    (values : ValueTable f xs us vs)
    (canonical : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1)
    (capWidths : ∀ row ∈ xs,∀ e ∈ row,e.2.length ≤ W)
    (amountWidths : ∀ u ∈ us,∀ v ∈ vs,(max (c u v) (c v u)).size ≤ W)
    (initial : BitState 92) (bound : initial.Bounded H A) (hp : initial.pc=14) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : StoredTable (eraseState initial).heap (eraseState initial).registers.a xs) :
    ∃ charge out,Run program (steps xs+1) charge initial [] out ∧
      GraphAdjacencyProgram.Matrix (eraseState out).heap (eraseState out).registers.d
        (residualFlags f us vs) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=15 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 92 H A (instructionBound us.length vs.length W) := by
  let old := eraseState initial
  obtain ⟨ext,root,hrep,hbody⟩ := natural_matrix input canonical old.source
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  let final := state (old.heap++ext) (old.registers.set .r3 root) [] old.source 15
  have trace : NaturalRun program (steps xs+1) old [] final := by
    rw [at_entry old hp empty hn]
    exact hbody
  have halt : tickNatural program final=none := rfl
  obtain ⟨charge,out,hr,hout,hstop,hcharge,htape⟩ := terminating_simulation bound trace halt
  refine ⟨charge,out,hr,?_,htape,?_,?_,⟨ext,?_⟩,hstop,hcharge.trans ?_⟩
  · rw [hout,← flags_eq f values]
    exact hrep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl
  · have width (row : List Entry) (hrow : row ∈ xs) :
        row.length=vs.length ∧ ∀ e ∈ row,e.1.magnitude.length ≤ W ∧ e.2.length ≤ W := by
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hrow
      have hu : i < us.length := by rwa [← values.length_eq]
      have rel := values.get hi hu
      refine ⟨rel.length_eq,?_⟩
      intro e he
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp he
      have hv : j < vs.length := by rwa [← rel.length_eq]
      have field := rel.get hj hv
      exact ⟨(ResidualCapacityProgram.amount_width f us[i] vs[j] _ field.1 (canonical _ hrow _ he)).trans
        (amountWidths _ (List.getElem_mem hu) _ (List.getElem_mem hv)),capWidths _ hrow _ he⟩
    have k := steps_le xs vs.length W width
    rw [values.length_eq] at k
    unfold completeBound runBound stepBound
    gcongr

end DirectedFlowCutGap.ResidualMatrixProgram
