import DirectedFlowCutGap.RoundStateUpdateProgram
import DirectedFlowCutGap.PhysicalCoverExecution
import DirectedFlowCutGap.PhysicalCoverReader

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation RetainedGridState

private def pair (heap : Heap) (left right : Bits) : Heap × Bits :=
  (heap ++ [.pair left right],heap.length.bits)

private def flags (heap : Heap) : Bits → Heap × Bits
  | [] => (heap,[])
  | bit :: rest =>
    let (grown,tail) := flags heap rest
    pair (grown++[.flag bit]) grown.length.bits tail

private def table {α : Type} (store : Heap → α → Heap × Bits) (heap : Heap) : List α → Heap × Bits
  | [] => (heap,[])
  | x :: xs =>
    let (grown,tail) := table store heap xs
    let (ready,head) := store grown x
    pair ready head tail

def main : IO Unit := do
  let counts : Family 2 := #v[#v[#v[5,7], #v[3,11]], #v[#v[8,17], #v[41,32]]]
  let state : Data 2 := ⟨#v[#v[false,true], #v[true,false]], #v[false,false], counts, 1, 39⟩
  let demand : Pair 2 := (1,0)
  let sampled : Flags 2 := #v[false,true]
  let words := (RetainedMassTableProgram.pairOrder 2).map fun p =>
    (row counts p).toList.map fun value => value.bits ++ [false]
  let (heap,weights) := table (table flags) [.nil,.flag false] words
  let (heap,remaining) := table flags heap (state.remaining.toList.map Vector.toList)
  let (heap,oldCut) := flags heap state.cut.toList
  let (heap,sampledRoot) := flags heap sampled.toList
  let (heap,masks) := pair heap remaining oldCut
  let (heap,rowIndex) := pair heap [] []
  let (heap,indices) := pair heap rowIndex []
  let (heap,context) := pair heap weights [true,false,false]
  let tape := [true, false, true, true]
  let start : BitState 402 := ⟨heap,heap.length.bits,⟨masks,indices,sampledRoot,context⟩,[],0,tape⟩
  let k := RoundStateUpdateProgram.steps state demand sampled words
  let run := fun fuel => PhysicalCoverExecution.executeCached RoundStateUpdateProgram.program fuel start 0
  let some (out,charge) := run (k+1)
    | throw (IO.userError "the combined physical update did not reach its paid stop")
  let stop := eraseState out
  let some (.pair outMasks mass) := stop.heap[stop.registers.d]?
    | throw (IO.userError "the updated state lacks its mass and mask roots")
  let some (.pair outRemaining outCut) := stop.heap[outMasks]?
    | throw (IO.userError "the updated state lacks a demand matrix or cut")
  let expected := (EncodedRoundingState.roundData state demand sampled).1
  let demands := PhysicalCoverReader.readList stop.heap (PhysicalCoverReader.readWord stop.heap) stop.heap.length outRemaining
  let cut := PhysicalCoverReader.readWord stop.heap outCut
  let massWord := PhysicalCoverReader.readWord stop.heap mass
  unless expected.current == 3 && massWord == some expected.current.bits &&
      demands == some (expected.remaining.toList.map Vector.toList) && cut == some expected.cut.toList &&
      (run k).isNone && out.pc == 5 && out.stack.isEmpty && out.source == tape &&
      out.heap.take heap.length == heap && 0 < charge do
    throw (IO.userError "the combined update changed the heap prefix, mask fields, mass or tape")
  IO.println s!"PASS full sampled-cut state update, mass {expected.current}, {k} successful instructions, paid {charge}"
