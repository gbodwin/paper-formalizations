import DirectedFlowCutGap.PhysicalSourceReadback

open DirectedFlowCutGap ImmutableReferenceSimulation

private def self : BinaryFractionalGuesses.Input 1 :=
  ⟨#v[#v[false]], [(0, 0)], #v[BinaryRational.one]⟩

private def wireHeap : Heap :=
  ([.pair 1 2, .nil, .pair 3 4, .pair 4 5, .nil, .pair 6 4,
   .pair 7 4, .pair 8 9, .pair 10 4, .pair 10 4, .flag true] : NaturalHeap).map
    (Cell.map Nat.bits)

def main : IO Unit := do
  match PhysicalSourceReadback.run self with
  | some (.infeasible (s, t), physical, lookups) =>
    unless s.val == 0 && t.val == 0 && 0 < physical && 0 < lookups do
      throw (IO.userError "the actual prefix lost its witness or one of its charges")
  | _ => throw (IO.userError "the actual physical prefix did not return its obstruction")
  match PhysicalCoverAccess.readPlan 1 wireHeap [] with
  | (some (.covers [row]), lookups) =>
    let x := row[0]
    unless x.num == 1 && x.den == 1 && 0 < lookups do
      throw (IO.userError "binary-pointer readback lost the best row or its lookup charge")
  | _ => throw (IO.userError "binary-pointer readback did not return the cover")
  IO.println "PASS charged terminal readback: physical witness and ordered positive cover"
