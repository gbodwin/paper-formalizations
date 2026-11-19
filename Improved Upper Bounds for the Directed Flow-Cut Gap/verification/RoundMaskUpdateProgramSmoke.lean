import DirectedFlowCutGap.RoundMaskUpdateProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation

def main : IO Unit := do
  let tape := [false, true, false, true]
  let no := [true, false, false]
  let heap : Heap := [
    .nil, .flag false, .flag true, .pair (2 : ℕ).bits [],
    .pair (1 : ℕ).bits (3 : ℕ).bits, .pair (2 : ℕ).bits (3 : ℕ).bits,
    .pair (5 : ℕ).bits [], .pair (4 : ℕ).bits (6 : ℕ).bits,
    .pair (7 : ℕ).bits (4 : ℕ).bits, .pair (3 : ℕ).bits (3 : ℕ).bits]
  let regs : Registers Bits := ⟨(8 : ℕ).bits, (9 : ℕ).bits, (5 : ℕ).bits, no⟩
  let init : BitState 92 := ⟨heap, (10 : ℕ).bits, regs, [], 0, tape⟩
  let execute := fun fuel => PhysicalCoverExecution.executeCached RoundMaskUpdateProgram.program fuel init 0
  let some (out, paid) := execute 71
    | throw (IO.userError "the combined mask update did not reach its paid stop")
  let expected := heap ++ [
    .pair no [], .pair (2 : ℕ).bits (10 : ℕ).bits,
    .pair (11 : ℕ).bits [], .pair (4 : ℕ).bits (12 : ℕ).bits,
    .pair (2 : ℕ).bits [], .pair (2 : ℕ).bits (14 : ℕ).bits,
    .pair (13 : ℕ).bits (15 : ℕ).bits]
  unless (execute 70).isNone && out.pc == 6 && out.stack.isEmpty && out.source == tape &&
      out.heap == expected && value out.registers.d == 16 && value out.next == 17 && 0 < paid do
    throw (IO.userError "the combined mask update changed its stored roots, allocation or tape")
  IO.println s!"PASS physical round mask update, 70 successful instructions, seven appended cells, paid {paid}"
