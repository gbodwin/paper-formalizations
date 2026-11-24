import DirectedFlowCutGap.MeasuredMultiplicityForms

open DirectedFlowCutGap
open RawNonnegativeRational (Code)

private def prices : FractionalCoverRawCore.RawRow 2 := #v[Code.ofNat 1,Code.ofNat 2]
private def current : FractionalCoverRawCore.RawRow 2 :=
  #v[Code.div Code.one (Code.ofNat 2),Code.div Code.one (Code.ofNat 4)]
private def choice : MultiplicityCover.Choice 2 := ⟨#v[2,1],0⟩

def main : IO Unit := do
  let update := MeasuredMultiplicityUpdate.run prices current choice
  let repr := update.1.toList.map (fun q => FractionalCoverRawCore.rational q)
  unless repr == [3/4,9/32] && update.2 > 0 do
    throw (IO.userError "the measured binary update did not produce the exact multiplicity factors")
  IO.println s!"PASS measured multiplicity update gave {repr} and charged {update.2}"
  let normalized := MeasuredMultiplicityForms.normalize current choice.column
  let length := MeasuredMultiplicityForms.lengthPaid current choice.column
  let objective := MeasuredMultiplicityForms.dot prices current
  let result := normalized.1.toList.map (fun q => FractionalCoverRawCore.rational q)
  unless result == [2/5,1/5] && FractionalCoverRawCore.rational length.1 == 5/4 &&
      FractionalCoverRawCore.rational objective.1 == 1 &&
      normalized.2 > 0 && objective.2 > 0 do
    throw (IO.userError "the measured length, normalization or objective changed the exact value")
  IO.println s!"PASS length 5/4, normalized row {result}, objective 1, and modeled charges {normalized.2}/{objective.2}"
