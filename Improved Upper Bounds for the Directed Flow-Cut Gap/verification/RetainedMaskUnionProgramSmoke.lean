import DirectedFlowCutGap.RetainedMaskUnionProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation

def main : IO Unit := do
  let tape := [true, false, true]
  let paddedTrue := [false, true, false, false]
  let heap : Heap := [
    .nil, .flag false, .flag true, .pair (2 : ℕ).bits [],
    .pair (1 : ℕ).bits (3 : ℕ).bits, .pair (2 : ℕ).bits (4 : ℕ).bits, .pair (1 : ℕ).bits (5 : ℕ).bits,
    .pair paddedTrue (3 : ℕ).bits, .pair (1 : ℕ).bits (7 : ℕ).bits, .pair (1 : ℕ).bits (8 : ℕ).bits]
  let initial : BitState 13 := ⟨heap, (10 : ℕ).bits, ⟨(6 : ℕ).bits ++ [false], (9 : ℕ).bits, [], []⟩, [], 0, tape⟩
  let execute := fun fuel => PhysicalCoverExecution.executeCached RetainedMaskUnionProgram.program fuel initial 0
  let some (out, paid) := execute 42
    | throw (IO.userError "retained mask union failed to reach its paid stop")
  let expected := heap ++ [
    .pair (2 : ℕ).bits [], .pair paddedTrue (10 : ℕ).bits,
    .pair (2 : ℕ).bits (11 : ℕ).bits, .pair (1 : ℕ).bits (12 : ℕ).bits]
  unless (execute 41).isNone && out.pc == 12 && out.stack.isEmpty && out.source == tape &&
      out.heap == expected && value out.registers.d == 13 && value out.next == 14 && 0 < paid do
    throw (IO.userError "retained union changed flag references, allocation or tape")
  IO.println s!"PASS physical retained cut union, 41 successful instructions, four appended cells, paid {paid}"
