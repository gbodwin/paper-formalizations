import DirectedFlowCutGap.CandidateRefreshProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation RetainedGridState

private abbrev Store := PackedWordPairTable.Prepared
private abbrev allocate := PackedWordPairTable.allocate
private abbrev word := PackedWordPairTable.word

private def storeList {α : Type} (item : α→Store→Store) : List α→Store→Store
  | [], s => allocate .nil s
  | x::xs, s =>
    let tail := storeList item xs s
    let head := item x tail
    allocate (.pair head.root tail.root) head

private def pair {n : ℕ} (p : Pair n) (s : Store) : Store :=
  let a := word p.1.val.bits s
  let b := word p.2.val.bits a
  allocate (.pair a.root b.root) b

private def readValues (heap : NaturalHeap) (root : ℕ) : Option (List ℕ) :=
  (PhysicalCoverReader.readList heap (PhysicalCoverReader.readWord heap) heap.length root).map (List.map value)

private def executeCounted {C : ℕ} (p : Program C) :
    ℕ→CachedReferenceExecution.FastState C→ℕ→ℕ→Option (BitState C×ℕ×ℕ)
  | 0, _, _, _ => none
  | fuel+1, s, steps, paid =>
    match CachedReferenceExecution.attempt p s with
    | .stopped final cost => some (final.freeze,steps,paid+cost)
    | .completed next => executeCounted p fuel next.state (steps+1) (paid+next.cost)

private def check (selection : Bool) (fuel : ℕ) : IO Unit := do
  let G : EncodedCandidateCapacity.Input 2 := ⟨#v[#v[false,false],#v[false,false]],#v[true,true]⟩
  let active : PairFlags 2 := #v[#v[false,selection],#v[false,false]]
  let seed := PackedWordPairTable.seed
  let matrix := storeList word (CandidatePortAdjacencyProgram.rows G) seed
  let n := word [false,true,false] matrix
  let graph := allocate (.pair matrix.root n.root) n
  let labels := storeList word [[],[true]] graph
  let grid := word [true,false] labels
  let labelsGrid := allocate (.pair labels.root grid.root) grid
  let shared := allocate (.pair graph.root labelsGrid.root) labelsGrid
  let mask := word G.removed.toList shared
  let scale := word [false] mask
  let state := allocate (.pair mask.root scale.root) scale
  let pairs := storeList pair (RetainedMassTableProgram.pairOrder 2) state
  let remaining := storeList word (active.toList.map Vector.toList) pairs
  let tape := [true,false,true]
  let input : BitState 4331 := ⟨remaining.heap,remaining.next,⟨pairs.root,remaining.root,shared.root,state.root⟩,[],0,tape⟩
  let some (out,k,paid) := executeCounted CandidateRefreshProgram.program fuel
      (CachedReferenceExecution.FastState.ofReference input) 0 0
    | throw (IO.userError "candidate family did not reach its charged halt")
  let final := eraseState out
  let some (.pair table mass) := final.heap[final.registers.d]?
    | throw (IO.userError "candidate refresh did not return the table and mass")
  let some refs := PhysicalCoverReader.readList final.heap some final.heap.length table
    | throw (IO.userError "candidate family did not return its table")
  let some values := refs.mapM (readValues final.heap) | throw (IO.userError "candidate row was unreadable")
  let expected := [[0,0],if selection then [1,1] else [0,0],[0,0],[0,0]]
  unless values == expected && refs[0]? == refs[2]? && refs[0]? == refs[3]? &&
      ((refs[0]? == refs[1]?) == !selection) && out.pc == 9 && out.stack.isEmpty && out.source == tape &&
      out.heap.take input.heap.length == input.heap && PhysicalCoverReader.readWord final.heap mass == some [] && 0 < paid &&
      k ≤ CandidateRefreshProgram.instructionBound 2 1 3 2 1 do
    throw (IO.userError s!"candidate family returned {values}, expected {expected}")
  IO.println s!"PASS physical candidate refresh, active (0, 1) = {selection}, rows {values}, optimum 0, {k} instructions, paid {paid}"

def main : IO Unit := do
  check false 1000
  check true 2500000
