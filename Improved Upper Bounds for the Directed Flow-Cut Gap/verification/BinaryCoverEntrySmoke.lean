import DirectedFlowCutGap.BinaryFractionalEntryCost

open DirectedFlowCutGap

private def bits (n : Nat) : BinaryArithmetic.Bits :=
  if n=0 then [] else decide (n%2=1)::bits (n/2)
termination_by n
decreasing_by omega

private def fraction (n d : Nat) : BinaryRational.Fraction :=
  ((BinaryRational.fromBits (bits n++[false,false]) (bits d++[false])).1).getD
    BinaryRational.zero

private def rowData {m : Nat} (r : FractionalCoverRawCore.RawRow m) : List (Nat × Nat) :=
  r.toList.map fun q => (q.num,q.den)

private def stateData {m : Nat} (s : FractionalCoverRawCore.RawState m) :=
  (rowData s.weights,rowData s.best,(s.bestCost.num,s.bestCost.den),
    (s.total.num,s.total.den),rowData s.loads,
    s.events.map fun e => (e.choice.column.toList.map Fin.val,e.choice.bottleneck.val,
      e.amount.num,e.amount.den))

#eval do
  let oracle : BinaryFractionalCore.Oracle 2 := fun _ => (⟨#v[true,false],0⟩,37)
  let rawOracle : FractionalCoverRawCore.RawOracle 2 := fun _ => ⟨{0},0⟩
  let mut cases : Nat := 0
  for a in List.range 4 do
    for b in List.range 4 do
      let c : BinaryFractionalRows.Row 2 := #v[fraction a 3,fraction b 5]
      let out := BinaryFractionalCore.solve c oracle (bits 2++[false,false])
      let fromInput := BinaryFractionalCore.solveInput c oracle
      let expected := FractionalCoverRawCore.solve (BinaryFractionalRows.decodeRow c) rawOracle
      unless stateData (BinaryFractionalCore.decodeState out.state)==stateData expected do
        throw (IO.userError "Binary cover recurrence changed a raw stored field or event")
      unless out.stopTests==12 do
        throw (IO.userError "A fixed-fuel stopping scan was skipped")
      unless stateData (BinaryFractionalCore.decodeState fromInput.state)==stateData expected &&
          fromInput.stopTests==12 do
        throw (IO.userError "Input-derived binary dimension or fuel changed the result")
      let maxInputBits := (c.toList.map fun q => max q.num.length q.den.length).foldl max 0
      unless fromInput.operations ≤ BinaryFractionalEntryCost.entryBound 2 maxInputBits 37 do
        throw (IO.userError "The full input/parameter/loop binary charge exceeded its polynomial bound")
      unless out.operations>12 do
        throw (IO.userError "Concrete scalar/array/controller charges were lost")
      cases := cases+1
  IO.println s!"PASS {cases} padded binary cover executions, full stored states/events, all 12 stopping scans"

#eval do
  let oracle : BinaryFractionalCore.Oracle 1 := fun _ => (⟨#v[true],0⟩,19)
  let c : BinaryFractionalRows.Row 1 := #v[fraction 1 1]
  let out := BinaryFractionalCore.solve c oracle (bits 1)
  unless out.stopTests==3 && out.state.events.length<out.stopTests do
    throw (IO.userError "The stopped-state test did not exercise remaining guard scans")
  IO.println s!"PASS stopped-state guard scans retained; events={out.state.events.length}, tests={out.stopTests}"
