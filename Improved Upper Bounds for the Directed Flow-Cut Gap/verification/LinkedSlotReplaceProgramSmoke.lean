import DirectedFlowCutGap.LinkedSlotReplaceProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation

def main : IO Unit := do
  let tape := [true, false, true]
  let paddedHead := [true, false, false]
  let replacement := [true, true, false, false]
  let heap : Heap := [
    .nil, .flag false, .flag true, .pair (1 : ℕ).bits [],
    .pair (2 : ℕ).bits (3 : ℕ).bits, .pair paddedHead (4 : ℕ).bits]
  let regs : Registers Bits := ⟨(5 : ℕ).bits, (3 : ℕ).bits, replacement, []⟩
  let init : BitState 14 := ⟨heap, (6 : ℕ).bits, regs, [], 0, tape⟩
  let execute := fun fuel => PhysicalCoverExecution.executeCached LinkedSlotReplaceProgram.program fuel init 0
  let some (out, paid) := execute 13
    | throw (IO.userError "linked slot replacement failed to halt")
  let expected := heap ++ [.pair replacement (3 : ℕ).bits, .pair paddedHead (6 : ℕ).bits]
  unless (execute 12).isNone && out.pc == 13 && out.stack.isEmpty && out.source == tape &&
      out.heap == expected && value out.registers.d == 7 && value out.next == 8 && 0 < paid do
    throw (IO.userError "linked replacement changed the payload, shared suffix, or tape")
  IO.println s!"PASS physical slot replacement, twelve successful instructions, two appended cells, paid {paid}"
