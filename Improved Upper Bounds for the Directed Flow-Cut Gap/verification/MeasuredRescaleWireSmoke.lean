import DirectedFlowCutGap.MeasuredRescaleWire

open DirectedFlowCutGap
open scoped NNRat

private def pack (q : ℚ≥0) : BinaryRational.Fraction :=
  (BinaryRawRational.encode (RawNonnegativeRational.Code.ofNNRat q)).1

def main : IO Unit := do
  let z := BinaryRational.zero
  let A : BinaryFractionalWalkOracle.Adjacency 3 :=
    #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
  let w : RationalEdgeThresholds.Weights 3 := #v[#v[z,pack (1/6),z],#v[z,z,pack (5/6)],#v[z,z,z]]
  let source := MeasuredRescaleWire.encode A w
  let suffix := [true,false,true]
  let tape := List.replicate 6 false ++ suffix
  let (some ⟨3,some ((some cut,drawFee),(rest,used))⟩,phaseFee) :=
      MeasuredRescaleWire.draw source 1 tape |
    throw (IO.userError "the checked frame failed to draw")
  unless decide (cut = {(1,2)}) && rest == suffix && used == 6 do
    throw (IO.userError "the accepted wire changed the exact cut or unread suffix")
  IO.println s!"PASS a {source.length}-bit source produced the reference cut after {used} tape bits, with preparation work {phaseFee} and draw charge {drawFee}"
  let (some ⟨3,none⟩,shortFee) := MeasuredRescaleWire.draw source 1 [false] |
    throw (IO.userError "the short tape was mistaken for a malformed frame or a completed trial")
  let (some ⟨3,some ((none,_),(rejectedRest,0))⟩,rejectedFee) := MeasuredRescaleWire.draw source 0 tape |
    throw (IO.userError "zero trials did not produce bounded rejection with a valid frame")
  unless rejectedRest == tape && shortFee == phaseFee && rejectedFee == phaseFee do
    throw (IO.userError "the tape outcome changed the measured deterministic prefix")
  IO.println "PASS short tape and bounded rejection remained distinct on a checked frame"
  let bad : EncodedEdgeInput.Input 3 :=
    ⟨A,[(0,2)],#v[z,pack (1/6),z,z,z,pack (5/6),z,z,z]⟩
  let trailing := MeasuredRescaleWire.draw (source ++ [false]) 1 tape
  let explicit := MeasuredRescaleWire.draw (EncodedEdgeInput.encode bad) 1 tape
  unless trailing.1.isNone && explicit.1.isNone && trailing.2 < phaseFee && explicit.2 < phaseFee do
    throw (IO.userError "a malformed source or nonempty explicit-demand field reached the sampler")
  IO.println s!"PASS trailing input and an explicit-demand field rejected before preparation at work {trailing.2} and {explicit.2}"
