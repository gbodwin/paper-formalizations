import DirectedFlowCutGap.MeasuredPaidSparsestRound

open DirectedFlowCutGap
open scoped NNRat
open BinaryArithmetic (Bits)
open BinaryRational (zero one)
open RawNonnegativeRational (Code)

private def fraction (q : ℚ≥0) : BinaryRational.Fraction :=
  (BinaryRawRational.encode (Code.ofNNRat q)).1

private def arcGraph : BinaryFractionalWalkOracle.Adjacency 2 :=
  #v[#v[false,true],#v[false,false]]

private def arcPrices : RationalEdgeThresholds.Weights 2 :=
  #v[#v[zero,fraction (5/7)],#v[zero,zero]]

private def arcRequests : Vector (Fin 2 × Fin 2) 1 := #v[(0,1)]

private def pathGraph : BinaryFractionalWalkOracle.Adjacency 3 :=
  #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]

private def vertexPrices : BinaryFractionalRows.Row 3 := #v[fraction 7,fraction (3/2),fraction 9]

private def demands : Vector (Fin 3 × Fin 3) 1 := #v[(0,2)]

private def separation : RetainedGridState.Flags 3 := #v[false,true,false]

private def tape : Bits := [true,false,true]

private def readOne : Bits → PhysicalCoverAccess.Read ((Bool × ℕ) × Bits)
  | [] => (none,7)
  | b::rest => (some ((b,13),rest),13)

private def checkSelection : IO Unit := do
  let score (b : Bool) := (if b then Code.one else Code.ofNat 2,29)
  let late := MeasuredTapeSelection.run readOne score 1 [false]
  let failedAttempts := PaidVertexAmplification.samplesWithCharges readOne 2 [false]
  let chosen := MeasuredTapeSelection.run readOne score 1 [false,true,false]
  let successfulAttempts := PaidVertexAmplification.samplesWithCharges readOne 2 [false,true,false]
  let tied (b : Bool) := (Code.one,if b then 17 else 19)
  let equal := MeasuredTapeSelection.run readOne tied 1 [false,true,false]
  unless late.1.isNone && late.2 == failedAttempts.1.2+failedAttempts.2 &&
      chosen.1 == some (true,[false]) && successfulAttempts.1.2+successfulAttempts.2 < chosen.2 &&
      equal.1 == some (false,[false]) do
    throw (IO.userError "paid selection changed the selected value, unread suffix, or exhausted charge")
  IO.println s!"PASS paid late exhaustion {late.2}; cheaper score and first tie kept [false], successful fee {chosen.2}"

private def checkScores : IO Unit := do
  let edgeMask : RationalSparsestEdgeRound.Mask 2 := #v[#v[false,true],#v[false,false]]
  let edge := MeasuredCutSparsity.edgeScore arcGraph arcPrices arcRequests edgeMask
  let vertex := MeasuredCutSparsity.vertexScore pathGraph vertexPrices demands separation
  let endpoints := MeasuredCutSparsity.vertexScore pathGraph vertexPrices demands #v[true,false,true]
  unless edge.1.value == 5/7 && vertex.1.value == 3/2 && endpoints.1.value == 0 &&
      0 < edge.2 && 0 < vertex.2 && 0 < endpoints.2 do
    throw (IO.userError "charged scores changed the original arc price or internal-vertex convention")
  IO.println s!"PASS actual arc score 5/7 with fee {edge.2}, internal score 3/2 with fee {vertex.2}, endpoints alone score zero"

private def checkEdge : IO Unit := do
  let arcMask : RationalSparsestEdgeRound.Mask 2 := #v[#v[false,true],#v[false,false]]
  let before := MeasuredPreparedSparsestRound.edge (by decide) arcGraph arcPrices arcRequests 1 1 tape
  let after := MeasuredPaidSparsestRound.edge (by decide) arcGraph arcPrices arcRequests 1 1 tape
  unless before.1 == some (arcMask,tape) && after.1 == before.1 && before.2 < after.2 do
    throw (IO.userError "paid edge execution changed the original mask or omitted the tape phase")
  IO.println s!"PASS original edge round kept its mask and all unread bits, preparation {before.2}, full modeled fee {after.2}"

private def checkVertex : IO Unit := do
  let before := MeasuredPreparedSparsestRound.vertex (by decide) pathGraph vertexPrices demands 1 1 tape
  let after := MeasuredPaidSparsestRound.vertex (by decide) pathGraph vertexPrices demands 1 1 tape
  unless before.1 == some (separation,tape) && after.1 == before.1 && before.2 < after.2 do
    throw (IO.userError "paid vertex execution changed the original mask or omitted the tape phase")
  IO.println s!"PASS original vertex round kept its internal cut and all unread bits, preparation {before.2}, full modeled fee {after.2}"
  let free : BinaryFractionalRows.Row 3 := #v[one,zero,one]
  let expected := MeasuredFreeResources.vertex pathGraph free demands
  let early := MeasuredPaidSparsestRound.vertex (by decide) pathGraph free demands 1 1 tape
  unless early.1 == some (separation,tape) && early.2 == expected.2 do
    throw (IO.userError "a free separating vertex consumed tape or charged skipped stages")
  IO.println s!"PASS free vertex skipped the optimizer and paid tape at fee {early.2}"

def main : IO Unit := do
  checkSelection
  checkScores
  checkEdge
  checkVertex
