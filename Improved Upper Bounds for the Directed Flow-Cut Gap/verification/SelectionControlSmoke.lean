import DirectedFlowCutGap.PaidVertexAmplification

open DirectedFlowCutGap BinaryArithmetic BinaryRational

def main : IO Unit := do
  let two : Fraction := ⟨(2 : ℕ).bits,[true],by decide⟩
  let costs : BinaryFractionalRows.Row 3 := #v[one,two,one]
  let a : RetainedGridState.Flags 3 := #v[true,false,true]
  let b : RetainedGridState.Flags 3 := #v[false,true,false]
  let c : RetainedGridState.Flags 3 := #v[true,true,true]
  let masks : Vector (EncodedVertexSolver.Output 3) 3 := #v[.cut a,.cut b,.cut c]
  let legacy := BinaryCutPriceSelection.minimum (BinaryCutPriceSelection.cutScore costs) 2 masks.get
  let actual := BinaryCutPriceSelection.minimumWithControl (BinaryCutPriceSelection.cutScoreWithControl costs) 2 masks.get
  let .cut selected := actual.1.value | throw (IO.userError "measured minimum returned a non-cut")
  let row := BinaryCutPriceSelection.maskFieldsWithControl costs a
  unless selected.toList == a.toList && actual.1.charge == legacy.charge &&
      actual.1.price.num == legacy.price.num && actual.1.price.den == legacy.price.den &&
      row.1.map (fun v => (value v.num,value v.den)) == [(1,1),(0,1),(1,1)] &&
      row.2 > 0 && actual.2 > row.2 do
    throw (IO.userError "measured minimum changed the first tied cut, price or field order")
  IO.println s!"PASS measured tied minimum retained the first equal-price cut, fee {actual.1.charge}, field work {row.2}, selection work {actual.2}"
  let input : BinaryFractionalGuesses.Input 3 :=
    ⟨#v[#v[false,false,false],#v[false,false,false],#v[false,false,false]],[],costs⟩
  let round : PaidVertexSampling.Runner 3 := fun _ _ _ => (none,5)
  let tape : Bits := [true,false,true]
  let old := PaidVertexAmplification.runWithPlanScalarWork input round 0 2 3 (.zero a) 7 11 tape
  let new := PaidVertexAmplification.runWithPlanSelectionWork input round 0 2 3 (.zero a) 7 11 tape
  let some out := new.1.1 | throw (IO.userError "measured selector was skipped after a completed walk")
  let .cut mask := out.output | throw (IO.userError "the selected plan returned a non-cut")
  unless mask.toList == a.toList && out.suffix == tape && out.dispatch == 7 && out.readback == 11 &&
      new.1.2 == old.1.2 && new.2 > old.2 do
    throw (IO.userError "amplified paid selection altered the output, phase fields or tape")
  IO.println s!"PASS one amplified price selection kept cut and suffix {out.suffix}, paid {new.1.2}, additional price work {new.2-old.2}"
