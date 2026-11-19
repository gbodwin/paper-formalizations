import DirectedFlowCutGap.RetainedEpochScheduleProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation

private def check (flags : Bits) (L : ℕ) (positive : 0<L) (expected : List ℕ) : IO Unit := do
  let initialStore := PackedWordPairTable.word flags PackedWordPairTable.seed
  let grid := PackedWordPairTable.word L.bits initialStore
  let tape := [true,false,true,false]
  let input : BitState 56 := ⟨grid.heap,grid.next,⟨initialStore.root,grid.root,[],[]⟩,[],36,tape⟩
  let k := RetainedEpochScheduleProgram.steps flags
  let p := RetainedEpochScheduleProgram.program
  let some (out,paid) := PhysicalCoverExecution.executeCached p (k+1) input 0
    | throw (IO.userError "the schedule did not reach its paid stop")
  let heap := eraseHeap out.heap
  let actual := PhysicalCoverReader.readList heap (PhysicalCoverReader.readWord heap) heap.length (value out.registers.d)
  let wanted := expected.map Nat.bits
  unless actual == some wanted && out.source == tape && out.pc == 31 && out.stack.isEmpty &&
      out.heap.take input.heap.length == input.heap && (PhysicalCoverExecution.executeCached p k input 0).isNone &&
      PhysicalEpochDraws.epochBounds L positive (RetainedEpochScheduleProgram.activeCount flags) == wanted && 0 < paid do
    throw (IO.userError "the physical schedule changed the bounds or tape")
  IO.println s!"PASS retained epoch schedule {flags}, bounds {expected}, {k} instructions, paid {paid}"

def main : IO Unit := do
  check [false,true,false,true,true] 5 (by decide) [3,2,1,5,5,5]
  check [false,false] 1 (by decide) []
  check [] 2 (by decide) []
