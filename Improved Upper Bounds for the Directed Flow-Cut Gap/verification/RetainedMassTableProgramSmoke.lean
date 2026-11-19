import DirectedFlowCutGap.RetainedMassTableProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation RetainedGridState

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

private def storeRows (heap : Heap) : List (List Bits) → Heap × Bits
  | [] => (heap, [])
  | row :: rest =>
    let (grown, tail) := storeRows heap rest
    let (ready, root) := storeWords grown row
    (ready ++ [.pair root tail], ready.length.bits)

def main : IO Unit := do
  let counts : Family 2 := #v[#v[#v[5,7], #v[3,11]], #v[#v[8,17], #v[41,32]]]
  let words := (RetainedMassTableProgram.pairOrder 2).map fun p =>
    (row counts p).toList.map fun value => value.bits ++ [false]
  let active : PairFlags 2 := #v[#v[false,true], #v[true,false]]
  let flags := (RetainedMassTableProgram.pairOrder 2).map (flag active)
  let cut : Flags 2 := #v[false,true]
  let tape := [false, true, false, true]
  let (h, rowRoot) := storeRows [.nil] words
  let (h, activeRoot) := storeBits h flags
  let (heap, cutRoot) := storeBits h cut.toList
  let start : BitState 274 := ⟨heap, heap.length.bits, ⟨activeRoot,rowRoot,cutRoot,[]⟩, [], 0, tape⟩
  let k := RetainedMassTableProgram.steps cut.toList flags words + 1
  let execute := fun fuel => PhysicalCoverExecution.executeCached RetainedMassTableProgram.program fuel start 0
  let some (out, paid) := execute (k + 1)
    | throw (IO.userError "the retained mass table failed to reach its paid stop")
  let current := (EncodedRoundingState.mass active cut counts).1
  let result := PhysicalCoverReader.readWord (eraseHeap out.heap) (value out.registers.d)
  unless current == 11 && result == some current.bits && (execute k).isNone &&
      out.pc == 23 && out.stack.isEmpty && out.source == tape &&
      out.heap.take heap.length == heap && 0 < paid do
    throw (IO.userError "the mass table changed the represented active rows, result, or tape")
  IO.println s!"PASS full retained mass table, two active pairs, mass {current}, {k} successful instructions, paid {paid}"
