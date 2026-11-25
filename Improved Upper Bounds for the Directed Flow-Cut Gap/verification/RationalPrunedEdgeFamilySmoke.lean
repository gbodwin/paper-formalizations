import DirectedFlowCutGap.RationalPrunedEdgeFamily
import DirectedFlowCutGap.RationalTrimmedEdgeFamily
import DirectedFlowCutGap.BinaryRawRational

open DirectedFlowCutGap
open scoped NNRat
open RawNonnegativeRational (Code)
open BinaryRational (zero)

private def pack (q : ℚ≥0) : BinaryRational.Fraction :=
  (BinaryRawRational.encode (Code.ofNNRat q)).1

private def pathWithLoops : BinaryFractionalWalkOracle.Adjacency 3 :=
  #v[#v[true,true,false],#v[false,true,true],#v[false,false,true]]

private def lengths : RationalEdgeThresholds.Weights 3 :=
  #v[#v[pack (1/6),pack (1/6),zero],#v[zero,pack (1/6),pack (5/6)],#v[zero,zero,pack (1/6)]]

private def realArcs : Finset (Fin 3 × Fin 3) := {(0,1),(1,2)}

private def hits (X : Finset (Fin 3 × Fin 3)) : Bool :=
  decide (X ⊆ realArcs ∧ ((0,1) ∈ X ∨ (1,2) ∈ X))

def main : IO Unit := do
  let A := pathWithLoops
  let w := lengths
  let retained := RationalPrunedEdgeFamily.pruned A w
  let kept := RationalPositiveArcEdgeFamily.positiveArcs A retained
  unless !RationalTrimmedEdgeFamily.keepsDemands A w &&
      RationalEdgeThresholds.far A w (0,2) && RationalEdgeThresholds.far A retained (0,2) &&
      RationalPrunedEdgeFamily.preserves A w retained &&
      RationalPositiveArcEdgeFamily.count A w == 5 && decide (kept = realArcs) do
    throw (IO.userError "the arc-by-arc test lost a tight demand or kept a removable loop")
  IO.println "PASS the fixed trim rejected a tight demand; arc-by-arc pruning kept that demand and reduced five positive arcs to two"
  let possible := RationalExactEdgeOracle.candidates A (RationalEdgeThresholds.demands A retained) ∅
  let minimal := RationalInstanceEdgeFactor.minimalCuts possible
  unless minimal.length == 2 && minimal.length < possible.length &&
      RationalInstanceEdgeFactor.leastMinimal A retained == 1 do
    throw (IO.userError "the reduced factor search lost an undominated cut or returned the wrong factor")
  IO.println s!"PASS exact factor 1 after reducing {possible.length} cut constraints to {minimal.length}"
  let initial := (RationalPrunedEdgeFamily.familyFor A w).cuts
  let cuts := (RationalPrunedEdgeFamily.family A w).cuts
  unless 0 < cuts.length && cuts.length < initial.length && cuts.all hits do
    throw (IO.userError "the pruned family lost an original cut or failed to shorten the horizon")
  let width := FairBitWords.width cuts.length
  let suffix := [true,false,true]
  let bits := List.replicate width false ++ suffix
  match RationalPrunedEdgeFamily.draw A w 1 bits with
  | some ((some cut,_),(rest,used)) =>
    unless hits cut && rest == suffix && used == width do
      throw (IO.userError "the literal sampler lost the original cut or unread tape")
  | _ => throw (IO.userError "the literal sampler did not return a cut")
  IO.println s!"PASS original cut family shortened from {initial.length} to {cuts.length}; the sampled cut used {width} bits and kept its suffix"
