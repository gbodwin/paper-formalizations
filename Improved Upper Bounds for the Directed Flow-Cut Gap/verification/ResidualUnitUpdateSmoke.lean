import DirectedFlowCutGap.ResidualUnitUpdateProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation

private def check (z : Int) (down : Bool) (expected : Int) : IO Unit := do
  let mag := PackedWordPairTable.word z.natAbs.bits PackedWordPairTable.seed
  let sign := PackedWordPairTable.allocate (.flag (z < 0)) mag
  let signed := PackedWordPairTable.allocate (.pair mag.root sign.root) sign
  let direction := PackedWordPairTable.allocate (.flag down) signed
  let tape := [false,true]
  let initial : BitState 96 := ⟨direction.heap,direction.next,⟨signed.root,direction.root,[],[]⟩,[],14,tape⟩
  let k := ResidualUnitUpdateProgram.steps ⟨z < 0,z.natAbs.bits⟩ down + 1
  let run := fun cap => PhysicalCoverExecution.executeCached ResidualUnitUpdateProgram.program cap initial 0
  let some (out,q) := run (k+1)
    | throw (IO.userError "the signed augmentation did not halt")
  let stop := eraseState out
  let some (.pair root sig) := stop.heap[stop.registers.d]?
    | throw (IO.userError "the signed augmentation returned an unexpected cell")
  let seen := PhysicalCoverReader.readWord stop.heap root
  unless seen == some expected.natAbs.bits && stop.heap[sig]? == some (.flag (expected < 0)) &&
      expected == z+(if down then -1 else 1) && out.pc == 15 && out.stack.isEmpty && out.source == tape &&
      out.heap.take initial.heap.length == initial.heap && (run k).isNone && 0 < q do
    throw (IO.userError "unexpected signed augmentation, terminal state or charge")
  IO.println s!"PASS physical signed unit update {z} to {expected}, {k} instructions, paid {q}"

def main : IO Unit := do
  check 0 false 1
  check 0 true (-1)
  check (-1) false 0
  check 1 true 0
  check 7 false 8
  check (-7) true (-8)
  check (-8) false (-7)
  check 8 true 7
