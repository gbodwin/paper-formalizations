import DirectedFlowCutGap.RationalExactEdgeOracle

open DirectedFlowCutGap
open scoped NNRat

def main : IO Unit := do
  let adjacency : BinaryFractionalWalkOracle.Adjacency 3 :=
    #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
  let z := BinaryRational.zero
  let half : BinaryRational.Fraction := ⟨[true],[false,true],by decide⟩
  let weights : RationalEdgeThresholds.Weights 3 :=
    #v[#v[z,half,z],#v[z,z,half],#v[z,z,z]]
  let demand := (0,2)
  let reached := RationalEdgeThresholds.demands adjacency weights
  let prices (e : Fin 3 × Fin 3) : ℚ≥0 := if e == (0,1) then 5 else 2
  let reversed (e : Fin 3 × Fin 3) : ℚ≥0 := if e == (0,1) then 1/3 else 2
  let first := RationalExactEdgeOracle.run adjacency weights prices
  let second := RationalExactEdgeOracle.run adjacency weights reversed
  unless reached.contains demand && decide (first = {(1,2)}) && decide (second = {(0,1)}) do
    throw (IO.userError "minimum rational price or original threshold equality changed")
  IO.println "PASS exact edge selector hit the distance-one demand and selected the cheapest arc for both price assignments"
  unless (RationalExactEdgeOracle.select adjacency [(0,0)] prices).isNone do
    throw (IO.userError "a self-demand admitted an integral edge cut")
  IO.println "PASS exact edge selector rejected the infeasible self-demand"
