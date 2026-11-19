import DirectedFlowCutGap.IntegerCellTestProgram
import DirectedFlowCutGap.BinaryFractionalGraphBounds
import DirectedFlowCutGap.BinaryFractionalWalkBounds

/-!
# Physical midpoint membership for one vertex

The same fixed program runs graph recovery and consumes that returned
walk in the integer cell test. The represented graph, row, source and
target are explicit inputs. The instruction bound uses stored word widths
and graph size, so a later scan can reuse it after the heap grows.
-/

namespace DirectedFlowCutGap.IntegerLevelVertexProgram

open BinaryArithmetic BinaryRational BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState IntegralNetworkFlow
open IntegerDistanceFromPhysical (encodedRow)

def graphLabel (pc : Fin 1344) : Fin 1540 := ⟨10+pc.val, by omega⟩
def cellLabel (pc : Fin 186) : Fin 1540 := ⟨1354+pc.val, by omega⟩

def program : Program 1540 := fun pc =>
  if pc.val < 10 then
    match pc.val with
    | 0 => .call (graphLabel 1342) 1 .r0
    | 1 => .field .r1 .r3 true 2
    | 2 => .field .r2 .r3 false 3
    | 3 => .call (cellLabel 19) 4 .r3
    | 4 => .ret .r3
    | 8 => .call 0 9 .r3
    | _ => .halt
  else if pc.val = 1353 ∨ pc.val = 1374 then .ret .r3
  else if h : pc.val < 1354 then
    ReferenceProgramLabels.instruction graphLabel (GraphRecoveryController.program ⟨pc.val-10, by omega⟩)
  else
    ReferenceProgramLabels.instruction cellLabel (IntegerCellTestProgram.program ⟨pc.val-1354, by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (registers : Registers ℕ) (stack : List (Frame ℕ 1540))
    (tape : Bits) (pc : Fin 1540) : NaturalState 1540 :=
  ⟨heap,heap.length,registers,stack,pc,tape⟩

def LevelAndWeight (heap : NaturalHeap) (root : ℕ) (weight level : Bits) : Prop :=
  ∃ j w, heap[root]? = some (.pair j w) ∧ BoolList heap w weight ∧ BoolList heap j level

def witness {n : ℕ} (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : Row n) (s t : Fin n) (label : Fin n → Bits) : Option GraphWalkExtension.Walk :=
  (IntegerDistanceFromPhysical.shortest E adjacency a s t).map (GraphRelaxationRefinement.encode label)

def instructions {n : ℕ} (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : Row n) (s t : Fin n) (sw : Bits) (label : Fin n → Bits) (weight level : Bits) : ℕ :=
  GraphRecoveryController.steps (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
    (encodedRow a).toList sw (label t) (label s) +
  IntegerCellTestProgram.instructions (witness E adjacency a s t label) weight level + 9

def instructionBound (n W S : ℕ) : ℕ :=
  GraphRecoveryController.instructionBound n W S +
    IntegerCellTestProgram.instructionBound (n*(W+2)+W+1) + 8

private theorem graph_slots (pc : Fin 1344) (h : GraphRecoveryController.program pc ≠ .halt) :
    program (graphLabel pc) =
      ReferenceProgramLabels.instruction graphLabel (GraphRecoveryController.program pc) := by
  by_cases hp : pc.val = 1343
  · have eq : pc = 1343 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,graphLabel,show ¬10+pc.val<10 by omega,
      show 10+pc.val≠1353 by omega,show 10+pc.val≠1374 by omega,show 10+pc.val<1354 by omega]

private theorem cell_slots (pc : Fin 186) (h : IntegerCellTestProgram.program pc ≠ .halt) :
    program (cellLabel pc) = ReferenceProgramLabels.instruction cellLabel (IntegerCellTestProgram.program pc) := by
  by_cases hp : pc.val = 20
  · have eq : pc = 20 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,cellLabel,show ¬1354+pc.val<10 by omega,show 1354+pc.val≠1353 by omega,
      show 1354+pc.val≠1374 by omega,show ¬1354+pc.val<1354 by omega]

private theorem join {s u v : NaturalState 1540} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

theorem witness_value {n : ℕ} (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : Row n) (s t : Fin n) (label : Fin n → Bits) :
    IntegerDistanceFromPhysical.interpret (witness E adjacency a s t label) =
      (EncodedIntegerShortestPaths.distance E adjacency a s t).1 := by
  rw [← IntegerDistanceFromPhysical.result_eq E adjacency a s t]
  unfold witness
  cases IntegerDistanceFromPhysical.shortest E adjacency a s t <;> rfl

theorem instructions_le {n W : ℕ} (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : Row n) (s t : Fin n) (sw : Bits) (hs : value sw=s.val)
    (label : Fin n → Bits) (hlabel : ∀ i, value (label i)=i.val) (weight level : Bits)
    (hW : 1 ≤ W) (hsw : sw.length ≤ W) (labels : ∀ i, (label i).length ≤ W)
    (hrow : ∀ i : Fin n, a[i.val].bits.length ≤ W) (hw : weight.length ≤ W) (hj : level.length ≤ W) :
    instructions E adjacency a s t sw label weight level + 1 ≤ instructionBound n W sw.length := by
  have stored := IntegerDistanceFromPhysical.encodedRow_stored a W hW hrow
  have graphCost := GraphRecoveryController.steps_bound E adjacency (encodedRow a) s t sw hs label hlabel
    W hW hsw labels stored
  have each : ∀ i, StoredBounded (BinaryFractionalRows.get (encodedRow a) i) W := by
    intro i
    apply stored
    simp only [encodedRow,Vector.toList_ofFn,List.mem_ofFn,BinaryFractionalRows.get,Vector.getElem_ofFn]
    exact ⟨i,rfl⟩
  have paths := BinaryFractionalWalkBounds.shortest_stored E adjacency
    (BinaryFractionalGraphOracle.outgoing (encodedRow a) s)
    (BinaryFractionalGraphBounds.outgoing_stored (encodedRow a) each s) s t
  have width : ∀ q ∈ witness E adjacency a s t label, q.cost.num.length ≤ n*(W+2)+W+1 := by
    intro q hq
    obtain ⟨v,hv,rfl⟩ := Option.mem_map.mp hq
    have h := (paths v (Option.mem_def.mp hv)).1
    change v.cost.num.length ≤ _
    exact h.trans (by
      change n*(W+2)+1 ≤ n*(W+2)+W+1
      omega)
  have testCost := IntegerCellTestProgram.instructions_le (witness E adjacency a s t label) weight level
    (n*(W+2)+W+1) width (by omega) (by omega)
  unfold instructions instructionBound
  omega

theorem graph_return {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : Row n) (s t : Fin n) (sw : Bits) (hs : value sw=s.val)
    (label : Fin n → Bits) (hlabel : ∀ i, value (label i)=i.val)
    (input : GraphDiscoveryProgram.Vertices heap r.a (E.vertices.map label))
    (context : GraphDiscoveryProgram.GlobalContext heap r.b
      (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (encodedRow a).toList sw (label t))
    (src : BoolList heap r.c (label s))
    (caller : Frame ℕ 1540) (stack : List (Frame ℕ 1540)) (tape : Bits) :
    ∃ ext root, GraphDiscoveryProgram.StoredOption (heap++ext) root (witness E adjacency a s t label) ∧
      NaturalRun program (GraphRecoveryController.steps (E.vertices.map label)
        (GraphRelaxationRefinement.matrix adjacency) (encodedRow a).toList sw (label t) (label s) + 2)
        (state heap r (caller::stack) tape (graphLabel 1342)) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  have rows : n ≤ (GraphRelaxationRefinement.matrix adjacency).length := by
    simp [GraphRelaxationRefinement.matrix_length]
  have cols (i : ℕ) (hi : i < n) :
      n ≤ ((GraphRelaxationRefinement.matrix adjacency)[i]'(lt_of_lt_of_le hi rows)).length :=
    (GraphRelaxationRefinement.matrix_row_length adjacency ⟨i,hi⟩).ge
  have hv (u : Bits) (hu : u ∈ E.vertices.map label) : value u < n := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    rw [hlabel]
    exact i.isLt
  have ht : value (label t) < n := by rw [hlabel]; exact t.isLt
  have hc (u : Bits) (hu : u ∈ E.vertices.map label) : value u < (encodedRow a).toList.length := by
    simpa only [Vector.length_toList] using hv u hu
  let initial := GraphRecoveryController.state heap heap.length r.a r.b r.c r.d [] tape 1342
  obtain ⟨ext,root,_,hrun,hrep⟩ := GraphRecoveryController.shortest_high n initial rfl rfl rfl
    input context src rows cols hv ht hc (GraphRecoveryController.recovery_valid E adjacency (encodedRow a) s t sw hs label hlabel)
  rw [GraphRecoveryController.result_eq E adjacency (encodedRow a) s t sw hs label hlabel] at hrep
  have lifted := ReferenceProgramLabels.run graphLabel GraphRecoveryController.program program graph_slots hrun
  have lifted := ReferenceProgramStack.run program (caller::stack) lifted
  let before := state (heap++ext) ⟨r.a,r.b,r.c,root⟩ (caller::stack) tape (graphLabel 1343)
  let after := state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation
  have body : NaturalRun program (GraphRecoveryController.steps (E.vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) (encodedRow a).toList sw (label t) (label s) + 1)
      (state heap r (caller::stack) tape (graphLabel 1342)) [] before := by
    cases r
    simpa [initial,before,state,ReferenceProgramLabels.state,ReferenceProgramStack.state,
      GraphRecoveryController.state] using lifted
  have ret : tickNatural program before = some ⟨after,[],0⟩ := rfl
  exact ⟨ext,root,hrep,join body (.step ret (.done after))⟩

theorem vertex_subroutine {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : Row n) (s t : Fin n) (sw : Bits) (hs : value sw=s.val)
    (label : Fin n → Bits) (hlabel : ∀ i, value (label i)=i.val)
    (input : GraphDiscoveryProgram.Vertices heap r.a (E.vertices.map label))
    (context : GraphDiscoveryProgram.GlobalContext heap r.b
      (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (encodedRow a).toList sw (label t))
    (src : BoolList heap r.c (label s)) (weight level : Bits)
    (fields : LevelAndWeight heap r.d weight level)
    (caller : Frame ℕ 1540) (stack : List (Frame ℕ 1540)) (tape : Bits) :
    ∃ ext root, (heap++ext)[root]? = some (.flag
        (IntegerLevelCuts.cellTest (EncodedIntegerShortestPaths.distance E adjacency a s t).1 (value weight) (value level)).1) ∧
      NaturalRun program (instructions E adjacency a s t sw label weight level)
        (state heap r (caller::stack) tape 0) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  let saved := caller::stack
  let recovery : Frame ℕ 1540 := ⟨1,.r0,r⟩
  obtain ⟨eg,path,hpath,hg⟩ := graph_return E adjacency a s t sw hs label hlabel input context src recovery saved tape
  obtain ⟨j,w,pair,hw,hj⟩ := fields
  let mid := heap++eg
  let r1 := r.set .r0 path
  let r2 := r1.set .r1 w
  let args := r2.set .r2 j
  obtain ⟨ec,root,hflag,hrun⟩ := IntegerCellTestProgram.natural_cell hpath
    (boolList_extend hw eg) (boolList_extend hj eg) tape (r := ⟨path,w,j,r.d⟩)
  have heapPair := lookup_extend pair eg
  have callGraph : tickNatural program (state heap r saved tape 0) =
      some ⟨state heap r (recovery::saved) tape (graphLabel 1342),[],0⟩ := rfl
  have right : tickNatural program (state mid r1 saved tape 1) =
      some ⟨state mid r2 saved tape 2,[],0⟩ := by
    cases r
    simp [r1,r2,mid,tickNatural,program,state,Registers.get,Registers.set,heapPair]
  have left : tickNatural program (state mid r2 saved tape 2) =
      some ⟨state mid args saved tape 3,[],0⟩ := by
    cases r
    simp [r1,r2,args,mid,tickNatural,program,state,Registers.get,Registers.set,heapPair]
  let cellCaller : Frame ℕ 1540 := ⟨4,.r3,args⟩
  let actual := state (mid++ec) (args.set .r3 root) saved tape 4
  have callCell : tickNatural program (state mid args saved tape 3) =
      some ⟨state mid args (cellCaller::saved) tape (cellLabel 19),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run cellLabel IntegerCellTestProgram.program program cell_slots hrun
  have lift := ReferenceProgramStack.run program (cellCaller::saved) lift
  let bridged := state (mid++ec) (args.set .r3 root) (cellCaller::saved) tape (cellLabel 20)
  have cellTrace : NaturalRun program (IntegerCellTestProgram.instructions
      (witness E adjacency a s t label) weight level + 1)
      (state mid args (cellCaller::saved) tape (cellLabel 19)) [] bridged := by
    cases r
    simpa [args,r2,r1,mid,bridged,state,Registers.set,IntegerCellTestProgram.state,
      ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have cellRet : tickNatural program bridged = some ⟨actual,[],0⟩ := by
    cases r
    simp [bridged,actual,cellCaller,cellLabel,args,r2,r1,state,program,tickNatural,Registers.set,Registers.get]
  have ret : tickNatural program actual = some ⟨state (mid++ec)
      (caller.saved.set caller.destination root) stack tape caller.continuation,[],0⟩ := by
    cases r
    simp [actual,args,r2,r1,saved,state,program,tickNatural,Registers.set,Registers.get]
  refine ⟨eg++ec,root,?_,?_⟩
  · rw [← witness_value E adjacency a s t label, ← List.append_assoc]
    exact hflag
  · have trace := NaturalRun.step callGraph
        (join hg (NaturalRun.step right (NaturalRun.step left
          (NaturalRun.step callCell (join cellTrace (.step cellRet (.step ret (.done _))))))))
    unfold instructions
    convert trace using 1 <;> first | rfl | omega | simp only [mid,List.append_assoc]

theorem natural_vertex {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : Row n) (s t : Fin n) (sw : Bits) (hs : value sw=s.val)
    (label : Fin n → Bits) (hlabel : ∀ i, value (label i)=i.val)
    (input : GraphDiscoveryProgram.Vertices heap r.a (E.vertices.map label))
    (context : GraphDiscoveryProgram.GlobalContext heap r.b
      (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (encodedRow a).toList sw (label t))
    (src : BoolList heap r.c (label s)) (weight level : Bits)
    (fields : LevelAndWeight heap r.d weight level) (tape : Bits) :
    ∃ ext root, (heap++ext)[root]? = some (.flag
        (IntegerLevelCuts.cellTest (EncodedIntegerShortestPaths.distance E adjacency a s t).1 (value weight) (value level)).1) ∧
      NaturalRun program (instructions E adjacency a s t sw label weight level + 1)
        (state heap r [] tape 8) [] (state (heap++ext) (r.set .r3 root) [] tape 9) := by
  let frame : Frame ℕ 1540 := ⟨9,.r3,r⟩
  obtain ⟨ext,root,hflag,hrun⟩ := vertex_subroutine E adjacency a s t sw hs label hlabel
    input context src weight level fields frame [] tape
  have call : tickNatural program (state heap r [] tape 8) =
      some ⟨state heap r [frame] tape 0,[],0⟩ := rfl
  exact ⟨ext,root,hflag,.step call hrun⟩

private theorem at_entry (s : NaturalState 1540) (hp : s.pc=8) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s = state s.heap s.registers [] s.source 8 := by
  cases s
  simp_all [state]

theorem physical_vertex {n H A W : ℕ} (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : Row n) (s t : Fin n) (sw : Bits) (hs : value sw=s.val)
    (label : Fin n → Bits) (hlabel : ∀ i, value (label i)=i.val) (weight level : Bits)
    (hweight : value weight=a[t.val])
    (hW : 1 ≤ W) (hsw : sw.length ≤ W) (labels : ∀ i, (label i).length ≤ W)
    (hrow : ∀ i : Fin n, a[i.val].bits.length ≤ W) (hw : weight.length ≤ W) (hj : level.length ≤ W)
    (initial : BitState 1540) (hstate : initial.Bounded H A)
    (hp : initial.pc=8) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : GraphDiscoveryProgram.Vertices (eraseState initial).heap (eraseState initial).registers.a (E.vertices.map label))
    (context : GraphDiscoveryProgram.GlobalContext (eraseState initial).heap (eraseState initial).registers.b
      (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (encodedRow a).toList sw (label t))
    (src : BoolList (eraseState initial).heap (eraseState initial).registers.c (label s))
    (fields : LevelAndWeight (eraseState initial).heap (eraseState initial).registers.d weight level) :
    ∃ charge out, Run program (instructions E adjacency a s t sw label weight level+1) charge initial [] out ∧
      (eraseState out).heap[(eraseState out).registers.d]? = some (.flag
        (IntegerLevelCuts.cellTest (EncodedIntegerShortestPaths.distance E adjacency a s t).1 a[t.val] (value level)).1) ∧
      out.source = initial.source ∧ (eraseState out).stack = [] ∧ (eraseState out).pc = 9 ∧
      (∃ ext, (eraseState out).heap = (eraseState initial).heap++ext) ∧
      (attempt program out).result = none ∧
      charge + (attempt program out).operations ≤ completeBound 1540 H A (instructionBound n W sw.length) := by
  let old := eraseState initial
  obtain ⟨ext,root,hflag,hrun⟩ := natural_vertex E adjacency a s t sw hs label hlabel
    input context src weight level fields old.source
  let final := state (old.heap++ext) (old.registers.set .r3 root) [] old.source 9
  have hnil : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have entry := at_entry old hp hnil hn
  have trace : NaturalRun program (instructions E adjacency a s t sw label weight level+1) old [] final := by
    rw [entry]
    exact hrun
  have halt : tickNatural program final = none := rfl
  obtain ⟨charge,out,hactual,hout,hstop,hcharge,htape⟩ := terminating_simulation hstate trace halt
  refine ⟨charge,out,hactual,?_,htape,?_,?_,⟨ext,?_⟩,hstop,hcharge.trans ?_⟩
  · rw [hout,← hweight]; exact hflag
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl
  · have steps := instructions_le E adjacency a s t sw hs label hlabel weight level hW hsw labels hrow hw hj
    unfold completeBound runBound stepBound
    gcongr

end DirectedFlowCutGap.IntegerLevelVertexProgram
