import DirectedFlowCutGap.BinaryMaskProjections
import DirectedFlowCutGap.BinaryPayloadBlockMove
import DirectedFlowCutGap.BinaryPortPreparation

open DirectedFlowCutGap BinaryArithmetic EncodedUnitCostReplication
open RawNonnegativeRational (Code)

private def projections : IO Unit := do
  let d : Input 2 := ⟨#v[#v[false,true],#v[false,false]],#v[Code.one,Code.one],#v[Code.zero,Code.zero]⟩
  let ready := (BinaryPortPreparation.prepareAndReduce d).1
  let .zero flags _ := ready.reduced | throw (IO.userError "the port input should have zero objective")
  let start : ℕ := 2^100-4
  let made := BinaryIndexList.forMask flags start
  let checked := BinaryIndexList.checkedMask flags start
  let port := BinaryMaskProjections.core ready.prepared flags start
  let reference := ready.prepared.pullbackMaskWithCost flags
  unless made.nodes.length == ready.prepared.size && (value made.stop).size == 101 &&
      made.nodes.map (fun x => value x.index) == List.range ready.prepared.size &&
      (checked.1.map (List.map Fin.val)) == some (List.range ready.prepared.size) &&
      port.1.1.toList == [true,true] && port.1 == reference do
    throw (IO.userError "the reached port mask or binary index list changed")
  IO.println s!"PASS binary list checked {made.nodes.length} indexes at a 101-bit extent, charge {checked.2}, port mask {port.1.1.toList}, retained fee {port.1.2}, measured {port.2}"
  let k : Vector ℕ 3 := #v[1,2,0]
  let labels := labelVector k
  let selection := Vector.ofFn (n := labels.size) fun i => decide (i.val≠1)
  let complete := BinaryMaskProjections.fiber labels selection 0
  unless complete.1.1.toList == [true,false,true] && complete.1 == fullFiberMaskWithCost k labels selection do
    throw (IO.userError "partial and empty fibers lost the reference behavior")
  let rejected := BinaryIndexList.decodeWithWork [true] (by decide : value [true]=1)
    [⟨[],[true],none⟩,⟨[],[],none⟩]
  unless rejected.1.isNone do
    throw (IO.userError "an out-of-range encoded index was accepted")
  IO.println s!"PASS full and partial clone fibers and the empty fiber give {complete.1.1.toList}, retained fee {complete.1.2}, measured {complete.2}, invalid first index charged {rejected.2}"

private def memory : IO Unit := do
  let base : ℕ := 2^100-4
  let words : List Bits := [[],[false,false],[true,false,true,false]]
  let original : BinaryPayloadStore.Store := ⟨(base+3).bits,
    (words.zipIdx).map fun (p,i) => ⟨(base+i).bits,p⟩⟩
  let room := BinaryPayloadStore.allocate original (3 : ℕ).bits
  let copy := BinaryPayloadBlockMove.run base.bits room.1.2 room.1.1 words.length
  let some moved := copy.1 | throw (IO.userError "the initialized block did not copy")
  let source := (List.range 3).map fun i => (BinaryPayloadStore.read (base+i).bits moved.slots).1
  let destination := (List.range 3).map fun i => (BinaryPayloadStore.read (base+3+i).bits moved.slots).1
  let forbidden := BinaryPayloadStore.write moved moved.next [true]
  let gap : BinaryPayloadStore.Store := ⟨room.1.1.next,original.slots.take 1⟩
  let stopped := BinaryPayloadBlockMove.run base.bits room.1.2 gap words.length
  unless value moved.next == base+6 && (value moved.next).size == 101 &&
      source == words.map some && destination == source && moved.slots.length == 6 &&
      forbidden.1.isNone && stopped.1.isNone && stopped.2 < copy.2 do
    throw (IO.userError "the addressed copy changed a word, source slot, allocation or failed access")
  IO.println s!"PASS addressed allocation/copy kept {words} at both blocks with 101-bit extent, charges {room.2}/{copy.2}, missing source stopped at {stopped.2}, next address refused at {forbidden.2}"

def main : IO Unit := do
  projections
  memory
