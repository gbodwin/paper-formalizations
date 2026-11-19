import DirectedFlowCutGap.PhysicalBoundedDrawExecution
import DirectedFlowCutGap.PackedWordPairTable
import DirectedFlowCutGap.PhysicalCoverReader

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation
open PhysicalBoundedDrawProgram PhysicalBoundedDrawExecution

private def spine (emptyRoot : Bits) : ℕ → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | 0, s => {s with root := emptyRoot}
  | k+1, s =>
    let tail := spine emptyRoot k s
    PackedWordPairTable.allocate (.pair emptyRoot tail.root) tail

private def check (description : String) (fuel : ℕ) (tape : Bits)
    (expected : Option (ℕ × Bool × ℕ × Bits)) : IO Unit := do
  let bound : Bits := [true,true]
  let start := PackedWordPairTable.seed
  let word := PackedWordPairTable.word bound start
  let trials := spine start.root fuel word
  let s : BitState 78 := ⟨trials.heap,trials.next,⟨word.root,trials.root,[],[]⟩,[],18,tape⟩
  let budget := instructionBound bound.length fuel
  let raw := outcome bound fuel tape
  let tapeModel := EncodedSolverBits.run (LazyFairBitTrees.rejection 3 (by decide) fuel) tape
  let model := tapeModel.map fun (r,(rest,reads)) => (r.value.val,r.failed,reads,rest)
  unless model == expected do
    throw (IO.userError s!"the reference tree disagreed for {description}")
  let actual := GuardedReferenceExecution.execute program (budget+1) s 0
  match expected, actual with
  | none, none =>
    unless tape.length < raw.requests.length do
      throw (IO.userError s!"the guarded loop stopped too early for {description}")
    IO.println s!"PASS physical rejection {description}, empty input result"
  | some (n,failure,reads,rest), some (out,paid) =>
    let heap := eraseHeap out.heap
    let some (.pair index tag) := heap[value out.registers.d]?
      | throw (IO.userError s!"missing draw record for {description}")
    let some digits := PhysicalCoverReader.readWord heap index
      | throw (IO.userError s!"missing draw index for {description}")
    let k := instructions bound fuel tape+1
    unless value digits == n && heap[tag]? == some (.flag failure) &&
        out.source == rest && out.pc == 19 && out.stack.isEmpty && out.heap.take s.heap.length == s.heap &&
        raw.requests == tape.take reads && raw.suffix == tape.drop reads &&
        (GuardedReferenceExecution.execute program k s 0).isNone && 0 < paid do
      throw (IO.userError s!"the guarded draw changed its result for {description}")
    IO.println s!"PASS physical rejection {description}, {reads} requests, {k} instructions, paid {paid}"
  | _, _ => throw (IO.userError s!"the guarded draw changed its stopping result for {description}")

def main : IO Unit := do
  check "first trial" 2 [false,true,true] (some (2,false,2,[true]))
  check "one rejection" 2 [true,true,true,false,false,true] (some (1,false,4,[false,true]))
  check "legal zero default" 2 [true,true,true,true,false] (some (0,true,4,[false]))
  check "zero trials" 0 [true] (some (0,true,0,[true]))
  check "short initial word" 2 [true] none
  check "short word after rejection" 2 [true,true,false] none
