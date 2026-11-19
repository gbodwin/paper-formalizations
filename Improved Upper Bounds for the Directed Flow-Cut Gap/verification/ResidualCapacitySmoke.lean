import DirectedFlowCutGap.ResidualCapacityProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation

private def check (z : BinarySigned.Signed) (cap : Bits) (expected : Bool) : IO Unit := do
  let mag := PackedWordPairTable.word z.magnitude PackedWordPairTable.seed
  let sign := PackedWordPairTable.allocate (.flag z.negative) mag
  let signed := PackedWordPairTable.allocate (.pair mag.root sign.root) sign
  let capacity := PackedWordPairTable.word cap signed
  let tape := [true,false,true]
  let input : BitState 60 := ⟨capacity.heap,capacity.next,⟨signed.root,capacity.root,[],[]⟩,[],0,tape⟩
  let k := ResidualCapacityProgram.instructions z cap
  let p := ResidualCapacityProgram.program
  let some (out,q) := PhysicalCoverExecution.executeCached p (k+1) input 0
    | throw (IO.userError "the residual test did not halt")
  let actual := (eraseHeap out.heap)[value out.registers.d]?
  unless actual == some (.flag expected) && ResidualCapacityProgram.residual z cap == expected &&
      out.pc == 10 && out.stack.isEmpty && out.source == tape && out.heap.take input.heap.length == input.heap &&
      (PhysicalCoverExecution.executeCached p k input 0).isNone && 0 < q do
    throw (IO.userError "the residual edge test disagreed, altered the tape or skipped its terminal charge")
  IO.println s!"PASS fixed residual flow {BinarySigned.decode z} capacity {value cap}, {expected}, {k} instructions, paid {q}"

def main : IO Unit := do
  check ⟨true,[true]⟩ [false] true
  check ⟨false,[true,true]⟩ [false,false,true,false] true
  check ⟨false,[true,true]⟩ [true,true,false] false
  check ⟨false,[true,true]⟩ [false,true,false] false
  check ⟨false,[]⟩ [] false
