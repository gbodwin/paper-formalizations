import DirectedFlowCutGap.FramedEdgeStorage

open DirectedFlowCutGap BinaryArithmetic EncodedArrayStorage

def main : IO Unit := do
  let input : EncodedEdgeInput.Input 1 := ⟨#v[#v[true]],[],#v[BinaryRational.one]⟩
  let source := EncodedEdgeInput.encode input
  unless (PhysicalSourceInputJoin.edge source).1.isSome &&
      (PhysicalSourceInputJoin.edge (source++[true])).1.isNone do
    throw (IO.userError "the framed input did not distinguish acceptance and trailing source rejection")
  let prices := (PhysicalBinaryEdgeWire.decodeWithCost input).1
  let line := (PhysicalAmplifiedBinaryEdge.lineWithCost prices).1
  unless prices.costs[0][0].num == 1 && line.adjacency.toList.length == 3 do
    throw (IO.userError "the original price decoder and line preparation produced unexpected dimensions")
  let decoder := BinaryArrayNestedStorage.gridSchedule 1 1
  let preparation := PhysicalLineStorage.lineSchedule 1
  let start := 11
  let code := decoder++preparation
  let prior := allocateTrace start code
  let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
  let blocks := binary.blocks.map fun (base,count) => (value base,value count)
  unless decoder.length == 16 && fresh decoder == 12 && preparation.length == 210 && fresh preparation == 119 &&
      blocks.take 4 == [(11,3),(14,3),(17,3),(20,3)] && blocks.length == 32 && value binary.stop == 142 &&
      value binary.stop == prior.1 && blocks == prior.2 do
    throw (IO.userError "the binary reservation replay changed the row-before-parent order or extent")
  IO.println s!"PASS original one-vertex price and line schedules use {code.length} instructions and {fresh code} cells, with {blocks.length} reservations from {start} to {value binary.stop}"
  let empty := BinaryArrayNestedStorage.gridSchedule 0 0++PhysicalLineStorage.lineSchedule 0
  let before := allocateTrace 0 empty
  unless empty.length == 15 && fresh empty == 10 && before.1 == 10 && before.2.length == 5 do
    throw (IO.userError "the empty source lost an array reservation")
  IO.println "PASS zero-vertex price and line schedules reserve five headers and perform no row pushes"
