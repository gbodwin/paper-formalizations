import DirectedFlowCutGap.FramedPreparedRoundWork
import DirectedFlowCutGap.BinaryArrayPayloadCopy

open DirectedFlowCutGap BinaryArithmetic EncodedArrayStorage
open EncodedUnitCostReplication
open RawNonnegativeRational (Code)

private def mainInput : Input 2 :=
  ⟨#v[#v[false,true],#v[false,false]],#v[Code.one,Code.one],#v[Code.one,Code.one]⟩

private def prepare : IO Unit := do
  let mode := ChargedVertexModes.Mode.mass
  let p := (BinaryPortPreparation.prepareAndReduce mainInput).1
  let .replicated _ counts replica _ := p.reduced |
    throw (IO.userError "positive weighted input did not reach the replica")
  let uniform := (BinaryUniformArithmetic.compute replica.input).1
  let active := (BinaryRawRational.le Code.one uniform.total).1
  let code := RunnerPreparationLayout.code mode mainInput
  let start := 41
  let (last,blocks) := allocateTrace start code
  let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
  unless active && p.prepared.size == 6 && (cloneList counts).length == 6 &&
      (cloneList uniform.counts).length <= 6*(cloneList counts).length &&
      !(UniformPreparationArrays.chainCode replica.input).isEmpty &&
      last == start+fresh code && value binary.stop == last &&
      binary.blocks.map (fun (a,b) => (value a,value b)) == blocks do
    throw (IO.userError "weighted preparation changed its replica, chain or ordered reservations")
  IO.println s!"PASS reached weighted preparation retained {p.prepared.size} ports, {(cloneList counts).length} replicas and {(cloneList uniform.counts).length} chain labels, with {code.length} instructions and {blocks.length} reservations"
  let heavy := (BinaryHeavyPreparation.prepare mainInput).1.1
  let residual := (BinaryPortPreparation.prepareAndReduce heavy.data).1
  let .zero flags _ := residual.reduced | throw (IO.userError "empty residual did not take the zero branch")
  let sizeCode := RunnerPreparationLayout.code .size mainInput
  unless heavy.heavy.toList == [true,true] && heavy.size == 0 && flags.toList.isEmpty &&
      sizeCode.length < code.length do
    throw (IO.userError "the heavy branch failed to skip the replica and chain")
  IO.println s!"PASS heavy preparation retained its two heavy flags and no residual, with {sizeCode.length} instructions and no replica or chain"

private def payload : IO Unit := do
  let xs : List Bits := [[],[true,false,false],[false,true]]
  let destination : ℕ := 2^100-3
  let moved := BinaryArrayPayloadCopy.blockCopy 7 destination xs
  let visits := moved.trace.map BinaryArrayPayloadCopy.observe
  let expected := [(9,destination+2,[]),(10,destination+3,[true,false,false]),(11,destination+4,[false,true])]
  let last := destination+2+xs.length
  unless visits == expected && moved.trace.map BinaryArrayPayloadCopy.Slot.word == xs &&
      last.size == 101 && moved.charge <= BinaryArrayPayloadCopy.chargeBound xs.length last.size 3 do
    throw (IO.userError "the payload copy changed the word, address or accounted bound")
  IO.println s!"PASS three copied payload words kept empty and padded bits and crossed a 101-bit address boundary, with charge {moved.charge}"

def main : IO Unit := do
  prepare
  payload
