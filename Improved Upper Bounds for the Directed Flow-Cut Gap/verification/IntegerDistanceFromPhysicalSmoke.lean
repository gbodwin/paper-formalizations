import DirectedFlowCutGap.IntegerDistanceFromPhysical
import DirectedFlowCutGap.PhysicalCoverExecution
import DirectedFlowCutGap.PhysicalCoverReader
import DirectedFlowCutGap.PackedWordPairTable

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation RetainedGridState
open IntegralNetworkFlow

private def wordList : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [], p => PackedWordPairTable.allocate .nil p
  | x :: xs, p =>
    let tail := wordList xs p
    let head := PackedWordPairTable.word x tail
    PackedWordPairTable.allocate (.pair head.root tail.root) head

private def check {n : ℕ} (name : String) (adjacency : PairFlags n) (weights : Row n)
    (s t : Fin n) (expected : Option ℕ) : IO Unit := do
  let order := ResidualSearch.Enumeration.fin n
  let label := fun i : Fin n => i.val.bits ++ [false]
  let vertices := order.vertices.map label
  let matrix := GraphRelaxationRefinement.matrix adjacency
  let rows := (IntegerDistanceFromPhysical.encodedRow weights).toList
  let costs := PackedWordPairTable.construct (rows.map fun f => (f.num, f.den))
  let storedMatrix := wordList matrix costs
  let storedOrder := wordList vertices storedMatrix
  let sw := PackedWordPairTable.word (label s) storedOrder
  let tw := PackedWordPairTable.word (label t) sw
  let costsAndSource := PackedWordPairTable.allocate (.pair costs.root sw.root) tw
  let matrixAndCosts := PackedWordPairTable.allocate (.pair storedMatrix.root costsAndSource.root) costsAndSource
  let inputOrder := PackedWordPairTable.allocate (.pair storedOrder.root matrixAndCosts.root) matrixAndCosts
  let context := PackedWordPairTable.allocate (.pair tw.root inputOrder.root) inputOrder
  let tape := [true, false, true]
  let initial : BitState 1344 := ⟨context.heap,context.next,⟨storedOrder.root,context.root,sw.root,[]⟩,[],1342,tape⟩
  let k := GraphRecoveryController.steps vertices matrix rows (label s) (label t) (label s) + 1
  let some (out, cost) := PhysicalCoverExecution.executeCached GraphRecoveryController.program (k+1) initial 0
    | throw (IO.userError s!"the physical graph distance failed for {name}")
  let heap := eraseHeap out.heap
  let seen : Option (Option ℕ) := do
    match heap[value out.registers.d]? with
    | some .nil => some none
    | some (.pair _ costRoot) =>
      let some (.pair num den) := heap[costRoot]? | none
      let bs ← PhysicalCoverReader.readWord heap num
      let ds ← PhysicalCoverReader.readWord heap den
      if value ds == 1 then some (some (value bs)) else none
    | _ => none
  let model : Option ℕ := (EncodedIntegerShortestPaths.distance order adjacency weights s t).1
  unless model == expected && seen == some expected && out.pc == 1343 && out.stack.isEmpty &&
      out.source == tape && out.heap.take initial.heap.length == initial.heap && 0 < cost do
    throw (IO.userError s!"the physical shortest-path result changed the integer distance for {name}")
  IO.println s!"PASS fixed integer distance {name}, {k} instructions, paid {cost}"

def main : IO Unit := do
  let adjacency : PairFlags 3 := #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
  let weights : Row 3 := #v[101,3,53]
  check "interior" adjacency weights 0 2 (some 3)
  check "adjacent" adjacency weights 0 1 (some 0)
  check "unreachable" adjacency weights 2 0 none
  check "self" adjacency weights 0 0 (some 0)
