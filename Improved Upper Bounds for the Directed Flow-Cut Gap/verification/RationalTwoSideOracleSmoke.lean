import DirectedFlowCutGap.RationalTwoSideOracle

open DirectedFlowCutGap
open scoped NNRat
open BinaryRational (zero)
open BinaryFractionalWalkOracle (Adjacency)
open RationalEdgeThresholds (Weights)
open RationalExactEdgeOracle (Edge)

private def half : BinaryRational.Fraction := ⟨[true],[false,true],by decide⟩

private def twoTails : IO Unit := do
  let A : Adjacency 4 :=
    #v[#v[false,true,false,true],#v[false,false,true,false],
       #v[false,false,false,false],#v[false,false,false,false]]
  let w : Weights 4 :=
    #v[#v[zero,half,zero,zero],#v[zero,zero,half,zero],
       #v[zero,zero,zero,zero],#v[zero,zero,zero,zero]]
  let side (e : Edge 4) := e.1 == 1
  let price (first second : ℚ≥0) (e : Edge 4) : ℚ≥0 :=
    if e = (0,1) then first else if e = (1,2) then second else 100
  let levels := (RationalTwoSideOracle.levels A w side).length
  let cheapFirst := RationalTwoSideOracle.run A w side (price 1 8)
  let cheapSecond := RationalTwoSideOracle.run A w side (price 8 1)
  unless levels == 9 && decide (cheapFirst = some {(0,1)} ∧ cheapSecond = some {(1,2)}) do
    throw (IO.userError "the rational cut oracle missed the cheaper valid threshold")
  let autoFirst := RationalTwoSideOracle.runEndpoint A w (price 1 8)
  let autoSecond := RationalTwoSideOracle.runEndpoint A w (price 8 1)
  unless RationalInstanceEdgeFactor.endpointCap A w == 2 &&
      decide (autoFirst = cheapFirst ∧ autoSecond = cheapSecond) do
    throw (IO.userError "the executable endpoint partition changed the cheaper cut")
  IO.println s!"PASS {levels} sorted breakpoint and midpoint candidates, both price orders chose the cheaper unit-threshold arc and left the costly zero-length arc"


private def twoHeads : IO Unit := do
  let quarter : BinaryRational.Fraction := ⟨[true],[false,false,true],by decide⟩
  let A : Adjacency 4 :=
    #v[#v[false,false,true,false],#v[false,false,true,false],
       #v[false,false,false,true],#v[false,false,false,false]]
  let w : Weights 4 :=
    #v[#v[zero,zero,half,zero],#v[zero,zero,quarter,zero],
       #v[zero,zero,zero,half],#v[zero,zero,zero,zero]]
  let price (first second : ℚ≥0) (e : Edge 4) : ℚ≥0 :=
    if e = (0,2) then first else if e = (2,3) then second else 100
  let cheapFirst := RationalTwoSideOracle.runEndpoint A w (price 1 8)
  let cheapSecond := RationalTwoSideOracle.runEndpoint A w (price 8 1)
  unless RationalInstanceEdgeFactor.endpointCap A w == 2 &&
      decide (cheapFirst = some {(0,2)} ∧ cheapSecond = some {(2,3)}) do
    throw (IO.userError "the computed head partition missed the cheaper cut")
  IO.println "PASS the computed two-head partition chose each cheaper arc and avoided the costly subunit branch"

private def aboveCap : IO Unit := do
  let third : BinaryRational.Fraction := ⟨[true],[true,true],by decide⟩
  let A : Adjacency 4 :=
    #v[#v[false,true,false,false],#v[false,false,true,false],
       #v[false,false,false,true],#v[false,false,false,false]]
  let w : Weights 4 :=
    #v[#v[zero,third,zero,zero],#v[zero,zero,third,zero],
       #v[zero,zero,zero,third],#v[zero,zero,zero,zero]]
  unless RationalInstanceEdgeFactor.endpointCap A w == 3 &&
      (RationalTwoSideOracle.runEndpoint A w (fun _ => 1)).isNone do
    throw (IO.userError "the conditional oracle accepted a three-endpoint chain")
  IO.println "PASS the wrapper rejects a three-positive-endpoint chain"

private def zeroFactor : IO Unit := do
  let threeQuarter : BinaryRational.Fraction := ⟨[true,true],[false,false,true],by decide⟩
  let A : Adjacency 4 :=
    #v[#v[false,true,false,false],#v[false,false,false,false],
       #v[false,false,false,true],#v[false,false,false,false]]
  let w : Weights 4 :=
    #v[#v[zero,threeQuarter,zero,zero],#v[zero,zero,zero,zero],
       #v[zero,zero,zero,threeQuarter],#v[zero,zero,zero,zero]]
  unless RationalInstanceEdgeFactor.endpointCap A w == 2 &&
      decide (RationalTwoSideOracle.runEndpoint A w (fun _ => 1) = some ∅) do
    throw (IO.userError "the exact zero case did not return the empty cut")
  IO.println "PASS the exact zero-factor case returned the empty cut"

def main : IO Unit := do
  twoTails
  twoHeads
  aboveCap
  zeroFactor
