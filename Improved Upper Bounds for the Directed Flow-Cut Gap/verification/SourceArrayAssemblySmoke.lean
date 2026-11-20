import DirectedFlowCutGap.FramedVertexStorage

open DirectedFlowCutGap BinaryArithmetic
open EncodedVertexInput (Table)
open EncodedArrayStorage (Instruction allocateTrace fresh)

private def prices : Table := [([true,false],[true]),([true],[false,true])]
private def matrix : Table := [([false,true],[]),([false,false],[])]
private def demands : Table := [([],[true])]

private def reservations (code : List (Instruction Unit)) (copies : ℕ) : IO ℕ := do
  let start := 11
  let natural := allocateTrace start code
  let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
  unless code.length == copies && value binary.stop == natural.1 &&
      natural.1 == start+fresh code && binary.blocks.map (fun (a,b) => (value a,value b)) == natural.2 do
    throw (IO.userError "the modeled typed input arrays changed their reservations")
  return natural.1-start

def main : IO Unit := do
  let wire := PackingSourceInput.encode prices matrix demands
  let some ⟨n,vertex⟩ := (PhysicalSourceInputJoin.vertex wire).1 |
    throw (IO.userError "the original vertex source failed to assemble")
  unless n == 2 && vertex.costs.toList.map (fun q => (q.num,q.den)) == prices &&
      vertex.adjacency.toList.map Vector.toList == matrix.map Prod.fst &&
      vertex.demands.map (fun (a,b) => (a.val,b.val)) == [(0,1)] do
    throw (IO.userError "the original vertex source changed a padded price, row or demand")
  let vertexCells ← reservations (PhysicalSourceInputJoin.vertexArrayCode wire) 216
  let edgePrices := prices ++ prices.reverse
  let edgeWire := PackingSourceInput.encode edgePrices matrix demands
  let some ⟨m,ed⟩ := (PhysicalSourceInputJoin.edge edgeWire).1 |
    throw (IO.userError "the original edge source failed to assemble")
  unless m == n && ed.costs.toList.map (fun q => (q.num,q.den)) == edgePrices &&
      ed.adjacency.toList.map Vector.toList == matrix.map Prod.fst do
    throw (IO.userError "the original edge source changed its flat prices or rows")
  let edgeCells ← reservations (PhysicalSourceInputJoin.edgeArrayCode edgeWire) 282
  IO.println s!"PASS typed vertex and edge input arrays retained padded prices and ordered rows, 216/{vertexCells} and 282/{edgeCells} modeled copies/cells"
  let malformed := PackingSourceInput.encode prices [([false,true],[]),([false],[])] demands
  let trailing := wire++[true]
  unless (PhysicalSourceInputJoin.vertex malformed).1.isNone && (PhysicalSourceInputJoin.vertex trailing).1.isNone do
    throw (IO.userError "the typed input accepted a bad row or an extra suffix")
  let prefixCells ← reservations (PhysicalSourceInputJoin.vertexArrayCode malformed) 54
  let trailingCells ← reservations (PhysicalSourceInputJoin.vertexArrayCode trailing) 0
  IO.println s!"PASS rejected second row retained its modeled first-row copy, 54/{prefixCells}; rejected trailing input reserved {trailingCells} typed cells"
