import DirectedFlowCutGap.PhysicalVertexSolver

open DirectedFlowCutGap ImmutableReferenceSimulation

private def empty : BinaryFractionalGuesses.Input 0 := ⟨#v[], [], #v[]⟩

private def self : BinaryFractionalGuesses.Input 1 :=
  ⟨#v[#v[false]], [(0, 0)], #v[BinaryRational.one]⟩

private def sampleHeap : NaturalHeap :=
  [.pair 1 2, .nil, .pair 3 4, .pair 4 5, .nil, .pair 6 4,
   .pair 7 4, .pair 8 9, .pair 10 4, .pair 10 4, .flag true]

def main : IO Unit := do
  let bits := [true, false]
  let source := SourcePacking.encode empty.costs empty.adjacency empty.demands
  match PhysicalVertexSolver.source 0 (fun _ => EncodedSizeRounding.tree) source bits with
  | some ⟨n, .cut mask, (rest, used), paid⟩ =>
    unless n == 0 && mask.toList.isEmpty && rest == bits && used == 0 &&
        decide (0 < paid ∧ paid ≤ PhysicalSourceDispatch.paidBound empty) do
      throw (IO.userError "empty source did not retain the paid stop and random tape")
  | _ => throw (IO.userError "empty source did not return its zero cut")
  let source := SourcePacking.encode self.costs self.adjacency self.demands
  match PhysicalVertexSolver.source 0 (fun _ => EncodedWeightedRounding.tree) source bits with
  | some ⟨n, .infeasible (s, t), (rest, used), paid⟩ =>
    unless n == 1 && s.val == 0 && t.val == 0 && rest == bits && used == 0 &&
        decide (0 < paid ∧ paid ≤ PhysicalSourceDispatch.paidBound self) do
      throw (IO.userError "self demand lost its witness, paid stop, or random tape")
  | _ => throw (IO.userError "self demand did not return its obstruction")
  match PhysicalCoverReader.readPlan 1 sampleHeap 0 with
  | some (.covers [r]) =>
    let x := r[0]
    unless x.num == 1 && x.den == 1 do
      throw (IO.userError "the retained best row changed during readback")
  | _ => throw (IO.userError "the positive heap-reader fixture did not yield its cover row")
  IO.println "PASS physical vertex source: paid degenerate dispatch, self demand, and retained row readback"
