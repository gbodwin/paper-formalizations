import DirectedFlowCutGap.PhysicalSourceReadback

open DirectedFlowCutGap
open BinaryArithmetic ImmutableReferenceSimulation

private def pointer (i : ℕ) : Bits := i.bits
private def link (i j : ℕ) : Cell Bits := .pair (pointer i) (pointer j)

private def sampleHeap : Heap :=
  [.nil,.flag true,.flag false,link 1 0,link 2 0,link 1 4,link 2 5,link 5 6,
    link 7 0,link 8 0,link 0 9,link 10 0,link 0 11,link 0 3,link 2 13,link 1 5]

private def sampleStore (heap : Heap) : CachedReferenceHeap.Store :=
  heap.foldl CachedReferenceHeap.push CachedReferenceHeap.empty

private def source : BinaryFractionalGuesses.Input 2 :=
  let q : BinaryRational.Fraction := ⟨[true,false,false],[false,true,false,false],by decide⟩
  ⟨#v[#v[false,true],#v[false,false]], [(0,1),(1,0),(0,1)],#v[q,BinaryRational.one]⟩

def main : IO Unit := do
  let serialized := BinarySourceSerialization.run source
  let old := PhysicalSourceDispatch.input source
  let fuel := BinarySourceFuel.compute serialized.1.length
  unless serialized.1 == old && 0 < serialized.2 && 0 < fuel.2 &&
      PhysicalSourceDispatch.steps source < fuel.1 do
    throw (IO.userError "serialized source or dispatch fuel differed")
  IO.println s!"PASS padded and repeated ordered source fields, {serialized.1.length} bits, framing {serialized.2}, fuel {fuel.2}"
  let store := sampleStore sampleHeap
  let (some (.covers [row]),cost) := BinaryCoverReadback.readPlanCached 1 store (pointer 12) |
    throw (IO.userError "the terminal cover list did not parse")
  let some (.covers [oldRow]) := (PhysicalCoverAccess.readPlanCached 1 store (pointer 12)).1 |
    throw (IO.userError "the reference cover list did not parse")
  unless row[0].num == 1 && row[0].den == 2 && row[0].num == oldRow[0].num &&
      row[0].den == oldRow[0].den && (PhysicalCoverAccess.readPlanCached 1 store (pointer 12)).2 < cost &&
      cost == (BinaryCoverReadback.readPlan 1 sampleHeap (pointer 12)).2 do
    throw (IO.userError "the terminal cover row or count differed")
  IO.println s!"PASS padded terminal fraction decoded to exact 1/2 with a measured readback charge {cost}"
  let (some (.infeasible (a,b)),witnessCost) := BinaryCoverReadback.readPlanCached 2 store (pointer 14) |
    throw (IO.userError "the obstruction did not parse")
  let (some (.zero mask),maskCost) := BinaryCoverReadback.readPlanCached 2 store (pointer 15) |
    throw (IO.userError "the mask did not parse")
  unless a.val == 0 && b.val == 1 && mask.toList == [true,false] && 0 < witnessCost && 0 < maskCost do
    throw (IO.userError "the terminal obstruction or mask differed")
  let badStore := sampleStore (sampleHeap.set 7 (link 5 4))
  let bad := BinaryCoverReadback.readPlanCached 1 badStore (pointer 12)
  unless bad.1.isNone && (PhysicalCoverAccess.readPlanCached 1 badStore (pointer 12)).2 < bad.2 do
    throw (IO.userError "the zero denominator was accepted or its validation work was lost")
  IO.println "PASS terminal obstruction, mask, and counted zero-denominator rejection"
