import DirectedFlowCutGap.RetainedDemandEraseProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation

def main : IO Unit := do
  let tape := [true, false, true]
  let no := [true, false, false]
  let heap : Heap := [
    .nil, .flag false, .flag true, .pair (2 : ℕ).bits [],
    .pair (1 : ℕ).bits (3 : ℕ).bits, .pair (2 : ℕ).bits (3 : ℕ).bits,
    .pair (5 : ℕ).bits [], .pair (4 : ℕ).bits (6 : ℕ).bits]
  let regs : Registers Bits := ⟨(7 : ℕ).bits, (3 : ℕ).bits, (3 : ℕ).bits, no⟩
  let init : BitState 64 := ⟨heap, (8 : ℕ).bits, regs, [], 0, tape⟩
  let execute := fun fuel => PhysicalCoverExecution.executeCached RetainedDemandEraseProgram.program fuel init 0
  let some (out, paid) := execute 36
    | throw (IO.userError "fixed demand erase did not reach its paid stop")
  let expected := heap ++ [
    .pair no [], .pair (2 : ℕ).bits (8 : ℕ).bits,
    .pair (9 : ℕ).bits [], .pair (4 : ℕ).bits (10 : ℕ).bits]
  unless (execute 35).isNone && out.pc == 2 && out.stack.isEmpty && out.source == tape &&
      out.heap == expected && value out.registers.d == 11 && value out.next == 12 && 0 < paid do
    throw (IO.userError "fixed demand erase changed another flag, the original heap or the tape")
  IO.println s!"PASS cleared one retained demand, 35 successful instructions, four appended cells, paid {paid}"
