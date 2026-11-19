import DirectedFlowCutGap.IntegerLevelCutProgram
import DirectedFlowCutGap.PhysicalCoverExecution
import DirectedFlowCutGap.PackedWordPairTable

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation RetainedGridState
open IntegralNetworkFlow

private def wordList : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [], p => PackedWordPairTable.allocate .nil p
  | x :: xs, p =>
    let tail := wordList xs p
    let head := PackedWordPairTable.word x tail
    PackedWordPairTable.allocate (.pair head.root tail.root) head

private def check {n : ℕ} (adjacency : PairFlags n) (weights : Row n)
    (s : Fin n) (level : ℕ) (expected : Bits) : IO Unit := do
  let order := ResidualSearch.Enumeration.fin n
  let label := fun i : Fin n => i.val.bits ++ [false]
  let matrix := GraphRelaxationRefinement.matrix adjacency
  let rows := (IntegerDistanceFromPhysical.encodedRow weights).toList
  let costs := PackedWordPairTable.construct (rows.map fun f => (f.num, f.den))
  let storedMatrix := wordList matrix costs
  let storedOrder := wordList (order.vertices.map label) storedMatrix
  let sw := PackedWordPairTable.word (label s) storedOrder
  let j := level.bits ++ [false, false]
  let storedLevel := PackedWordPairTable.word j sw
  let costsAndSource := PackedWordPairTable.allocate (.pair costs.root sw.root) storedLevel
  let matrixAndCosts := PackedWordPairTable.allocate (.pair storedMatrix.root costsAndSource.root) costsAndSource
  let bundle := PackedWordPairTable.allocate (.pair storedOrder.root matrixAndCosts.root) matrixAndCosts
  let sourceLevel := PackedWordPairTable.allocate (.pair sw.root storedLevel.root) bundle
  let context := PackedWordPairTable.allocate (.pair bundle.root sourceLevel.root) sourceLevel
  let fields := IntegerLevelCutProgram.fields weights label (List.finRange n)
  let targets := fields.foldr PackedWordPairTable.prepend (PackedWordPairTable.allocate .nil context)
  let tape := [true,false,true]
  let initial : BitState 1572 := ⟨targets.heap,targets.next,⟨storedOrder.root,targets.root,context.root,[]⟩,[],0,tape⟩
  let k := IntegerLevelCutProgram.steps order adjacency weights s (label s) label j (List.finRange n) + 1
  let p := IntegerLevelCutProgram.program
  let some (out, paid) := PhysicalCoverExecution.executeCached p (k+1) initial 0
    | throw (IO.userError s!"physical cut scan did not halt at level {level}")
  let seen := PhysicalCoverReader.readWord (eraseHeap out.heap) (value out.registers.d)
  let model := (EncodedRoundingInput.cutFlags order adjacency weights s level).1.toList
  unless model == expected && seen == some expected && out.pc == 31 && out.stack.isEmpty &&
      out.source == tape && out.heap.take initial.heap.length == initial.heap &&
      (PhysicalCoverExecution.executeCached p k initial 0).isNone && 0 < paid do
    throw (IO.userError s!"physical cut scan returned the wrong mask at level {level}")
  IO.println s!"PASS full midpoint cut at level {level}, mask {expected}, {k} instructions, paid {paid}"

def main : IO Unit := do
  let adjacency : PairFlags 4 := #v[#v[false,true,false,false],#v[false,false,true,false],
    #v[false,false,false,false],#v[false,false,false,false]]
  let weights : Row 4 := #v[11,3,5,99]
  check adjacency weights 0 0 [true,true,false,false]
  check adjacency weights 0 4 [true,false,true,false]
  check adjacency weights 0 11 [false,false,false,false]
