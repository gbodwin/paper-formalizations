import DirectedFlowCutGap.RetainedMassRowProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation

private def storeBits (heap : Heap) : Bits → Heap × Bits
  | [] => (heap, [])
  | bit :: rest =>
    let (grown, tail) := storeBits heap rest
    (grown ++ [.flag bit, .pair grown.length.bits tail], (grown.length + 1).bits)

private def storeWords (heap : Heap) : List Bits → Heap × Bits
  | [] => (heap, [])
  | xs :: rest =>
    let (grown, tail) := storeWords heap rest
    let (ready, word) := storeBits grown xs
    (ready ++ [.pair word tail], ready.length.bits)

def main : IO Unit := do
  let words := [(3 : ℕ).bits ++ [false, false], (17 : ℕ).bits, (5 : ℕ).bits]
  let flags := [false, true, false]
  let tape := [true, false, false]
  let (h, row) := storeWords [.nil] words
  let (heap, cut) := storeBits h flags
  let start : BitState 134 := ⟨heap, heap.length.bits, ⟨row,cut,[],[]⟩, [], 0, tape⟩
  let k := RetainedMassRowProgram.steps words flags + 1
  let execute := fun fuel => PhysicalCoverExecution.executeCached RetainedMassRowProgram.program fuel start 0
  let some (out, paid) := execute (k + 1)
    | throw (IO.userError "the mass row did not reach the paid stop")
  let result := PhysicalCoverReader.readWord (eraseHeap out.heap) (value out.registers.d)
  unless (execute k).isNone && out.pc == 17 && out.stack.isEmpty && out.source == tape &&
      out.heap.take heap.length == heap && result == some (8 : ℕ).bits && 0 < paid do
    throw (IO.userError "the mass row changed the operand padding, mask, result or tape")
  IO.println s!"PASS retained mass 3+5=8 with 17 excluded, {k} successful instructions, paid {paid}"
