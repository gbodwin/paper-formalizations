import DirectedFlowCutGap.IntegerLevelVertexProgram
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

private def check {n : ℕ} (name : String) (adjacency : PairFlags n) (weights : Row n)
    (s t : Fin n) (level : ℕ) (expected : Bool) : IO Unit := do
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
  let j := level.bits ++ [false]
  let w := weights[t.val].bits ++ [false]
  let levelWord := PackedWordPairTable.word j context
  let weightWord := PackedWordPairTable.word w levelWord
  let args := PackedWordPairTable.allocate (.pair levelWord.root weightWord.root) weightWord
  let tape := [true,false,true]
  let initial : BitState 1540 :=
    ⟨args.heap,args.next,⟨storedOrder.root,context.root,sw.root,args.root⟩,[],8,tape⟩
  let k := IntegerLevelVertexProgram.instructions order adjacency weights s t (label s) label w j + 1
  let p := IntegerLevelVertexProgram.program
  let some (out, paid) := PhysicalCoverExecution.executeCached p (k+1) initial 0
    | throw (IO.userError s!"physical vertex test failed for {name}")
  let flag := (eraseHeap out.heap)[value out.registers.d]?
  let model := (EncodedRoundingInput.cutFlags order adjacency weights s level).1
  unless model[t.val] == expected && flag == some (.flag expected) && out.pc == 9 && out.stack.isEmpty &&
      out.source == tape && out.heap.take initial.heap.length == initial.heap &&
      (PhysicalCoverExecution.executeCached p k initial 0).isNone && 0 < paid do
    throw (IO.userError s!"physical vertex test disagreed with the cut flag for {name}")
  IO.println s!"PASS fused shortest path and midpoint {name}, {k} instructions, paid {paid}"

def main : IO Unit := do
  let adjacency : PairFlags 3 := #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
  let weights : Row 3 := #v[101,3,5]
  check "finite inside" adjacency weights 0 2 4 true
  check "finite below" adjacency weights 0 2 2 false
  check "finite upper boundary" adjacency weights 0 2 8 false
  check "unreachable" adjacency weights 2 0 4 false
