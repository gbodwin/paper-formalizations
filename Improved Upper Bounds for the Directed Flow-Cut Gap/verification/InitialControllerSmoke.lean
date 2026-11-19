import DirectedFlowCutGap.OriginalGraphControllerProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation RetainedGridState

private abbrev Store := PackedWordPairTable.Prepared
private abbrev allocate := PackedWordPairTable.allocate
private abbrev word := PackedWordPairTable.word

private def wordList : List Bits → Store → Store
  | [], s => allocate .nil s
  | w::ws, s =>
    let tail := wordList ws s
    let head := word w tail
    allocate (.pair head.root tail.root) head

private def pair (heap : NaturalHeap) (root : ℕ) : Option (ℕ×ℕ) :=
  match heap[root]? with
  | some (.pair a b) => some (a,b)
  | _ => none

private def execute {C : ℕ} (p : Program C) :
    ℕ → CachedReferenceExecution.FastState C → ℕ → ℕ → Option (BitState C×ℕ×ℕ)
  | 0, _, _, _ => none
  | fuel+1, s, steps, paid =>
    match CachedReferenceExecution.attempt p s with
    | .stopped final cost => some (final.freeze,steps,paid+cost)
    | .completed next => execute p fuel next.state (steps+1) (paid+next.cost)

private def build {n : ℕ} (adj : PairFlags n) (L : ℕ) (budgetCount : ℕ := 0) :
    Store × Bits × Bits × Bits := Id.run do
  let s := PackedWordPairTable.seed
  let adjMatrix := wordList (adj.toList.map Vector.toList) s
  let count := word n.bits adjMatrix
  let grid := word L.bits count
  let one := word [true] grid
  let fields := allocate (.pair grid.root one.root) one
  let dims := allocate (.pair count.root fields.root) fields
  let graph := allocate (.pair adjMatrix.root dims.root) dims
  let rs := word [false,false,true] graph
  let m := word [] rs
  let gates := allocate (.pair rs.root m.root) m
  let (extended,spine) := (List.range budgetCount).foldl
    (fun (state,root) _ => let next := allocate (.pair s.root root) state; (next,next.root))
    (gates,s.root)
  let fuel := allocate (.pair spine spine) extended
  let budget := allocate (.pair s.root fuel.root) fuel
  let controls := allocate (.pair gates.root budget.root) budget
  return (controls,graph.root,gates.root,controls.root)

private def checkMask (L : ℕ) (expect : List Bits) : IO Unit := do
  let adj : PairFlags 3 := #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
  let (data,graph,gates,_) := build adj L
  let source := [true,false]
  let init : BitState 3589 := ⟨data.heap,data.next,⟨graph,gates,[],[]⟩,[],0,source⟩
  let some (out,k,paid) := execute InitialSeedProgram.program 500000 (CachedReferenceExecution.FastState.ofReference init) 0 0
    | throw (IO.userError "initial graph preparation failed")
  let final := eraseState out
  let some (weightsRecord,controlRecord) := pair final.heap final.registers.d
    | throw (IO.userError "missing computed masks and weights")
  let some (mask,weights) := pair final.heap weightsRecord | throw (IO.userError "missing actual demand mask and weights")
  let some (cut,params) := pair final.heap controlRecord | throw (IO.userError "missing cut mask and parameters")
  let read := PhysicalCoverReader.readWord final.heap
  let readRows := PhysicalCoverReader.readList final.heap read final.heap.length
  let some refs := PhysicalCoverReader.readList final.heap some final.heap.length weights
    | throw (IO.userError "missing initial weights")
  unless out.pc == 10 && out.stack.isEmpty && out.source == source &&
      out.heap.take init.heap.length == init.heap &&
      readRows mask == some expect && read cut == some [false,false,false] && (pair final.heap params).isSome &&
      refs.length == 9 && refs.all (· == refs[0]?.getD 0) &&
      refs.mapM readRows == some (List.replicate 9 (List.replicate 3 [true])) do
    throw (IO.userError s!"incorrect original demand mask or uniform rows at threshold {L}: {repr (readRows mask)}")
  IO.println s!"PASS input path threshold {L}, actual demands {repr expect}, shared uniform rows, {k} instructions, paid {paid}"

private def checkInitialized : IO Unit := do
  let adj : PairFlags 2 := #v[#v[false,true],#v[true,false]]
  let (data,graph,_,controls) := build adj 1
  let tape := [false,true,true]
  let init : BitState 10935 := ⟨data.heap,data.next,⟨graph,controls,[],[]⟩,[],0,tape⟩
  let some (out,k,paid) := execute PhysicalControllerInitializer.program 500000 (CachedReferenceExecution.FastState.ofReference init) 0 0
    | throw (IO.userError "initial controller cache did not halt")
  let final := eraseState out
  let some (live,best) := pair final.heap final.registers.d | throw (IO.userError "missing initialized cache")
  let some (m,runtime) := pair final.heap live | throw (IO.userError "missing initialized runtime and masks")
  let some (masks,current) := pair final.heap m | throw (IO.userError "missing initialized mass")
  let some (active,cut) := pair final.heap masks | throw (IO.userError "missing initialized masks")
  let some (ctx,scale) := pair final.heap runtime | throw (IO.userError "missing initialized scale")
  let some (weights,free) := pair final.heap ctx | throw (IO.userError "missing initialized weight context")
  let some (table,opt) := pair final.heap best | throw (IO.userError "missing initialized optimizer")
  let read := PhysicalCoverReader.readWord final.heap
  let rows := PhysicalCoverReader.readList final.heap read final.heap.length
  let some wrefs := PhysicalCoverReader.readList final.heap some final.heap.length weights | throw (IO.userError "missing original weights")
  let some crefs := PhysicalCoverReader.readList final.heap some final.heap.length table | throw (IO.userError "missing refreshed candidates")
  unless out.pc == 7 && out.stack.isEmpty && out.source == tape && out.heap.take init.heap.length == init.heap &&
      final.heap[final.registers.a]? == some .nil && (pair final.heap final.registers.c).isSome &&
      rows active == some (List.replicate 2 [false,false]) && read cut == some [false,false] &&
      read current == some [] && read opt == some [] && read scale == some [true] &&
      final.heap[free]? == some (.flag false) &&
      wrefs.mapM rows == some (List.replicate 4 [[true],[true]]) &&
      crefs.mapM rows == some (List.replicate 4 [[],[]]) do
    throw (IO.userError "actual initialized state or initial cache is incorrect")
  IO.println s!"PASS original two-vertex graph initialized a zero-optimum cache and preserved the full tape, {k} instructions, paid {paid}"

private def checkOriginal : IO Unit := do
  let adj : PairFlags 2 := #v[#v[false,true],#v[true,false]]
  let (data,graph,_,controls) := build adj 1 2
  let tape := [false,true,true]
  let input : BitState 26259 := ⟨data.heap,data.next,⟨graph,controls,[],[]⟩,[],0,tape⟩
  let program := OriginalGraphControllerProgram.program
  let some (counted,steps,unguarded) := execute program 500000 (CachedReferenceExecution.FastState.ofReference input) 0 0
    | throw (IO.userError "original graph controller did not halt")
  let some (out,paid) := GuardedReferenceExecution.execute program (steps+1) input 0
    | throw (IO.userError "guarded original graph controller did not halt")
  let final := eraseState out
  let some (live,best) := pair final.heap final.registers.d | throw (IO.userError "missing final cache")
  let some (state,_) := pair final.heap live | throw (IO.userError "missing final state")
  let some (masks,current) := pair final.heap state | throw (IO.userError "missing final current mass")
  let some (active,cut) := pair final.heap masks | throw (IO.userError "missing final masks")
  let some (_,optimum) := pair final.heap best | throw (IO.userError "missing final optimum")
  let read := PhysicalCoverReader.readWord final.heap
  let rows := PhysicalCoverReader.readList final.heap read final.heap.length
  unless out == counted && out.pc == 26258 && out.stack.isEmpty && out.source == tape &&
      out.heap.take input.heap.length == input.heap && read cut == some [false,false] &&
      rows active == some [[false,false],[false,false]] && read current == some [] &&
      read optimum == some [] &&
      paid == unguarded+(steps+1)*GuardedReferenceExecution.guardCost 26259 do
    throw (IO.userError "the joined controller did not preserve the original heap, final cut, or fair tape")
  IO.println s!"PASS guarded original graph controller computed its cache and stopped before drawing with positive control spines, {steps} instructions, paid {paid}"

def main : IO Unit := do
  checkMask 1 [[false,false,true],[true,false,false],[true,true,false]]
  checkMask 2 [[false,false,false],[true,false,false],[true,true,false]]
  checkInitialized
  checkOriginal
