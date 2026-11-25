import DirectedFlowCutGap.RationalInstanceEdgeFactor

open DirectedFlowCutGap
open BinaryRational (zero)
open BinaryFractionalWalkOracle (Adjacency)
open RationalEdgeThresholds (Weights)
open RationalInstanceEdgeFactor (endpointCap leastSupportedWithCalls)

private def half : BinaryRational.Fraction := ⟨[true],[false,true],by decide⟩
private def quarter : BinaryRational.Fraction := ⟨[true],[false,false,true],by decide⟩

private def twoHeads : IO Unit := do
  let A : Adjacency 4 :=
    #v[#v[false,false,true,false],#v[false,false,true,false],
       #v[false,false,false,true],#v[false,false,false,false]]
  let w : Weights 4 :=
    #v[#v[zero,zero,half,zero],#v[zero,zero,quarter,zero],
       #v[zero,zero,zero,half],#v[zero,zero,zero,zero]]
  unless endpointCap A w == 2 && leastSupportedWithCalls A w == (1,0) do
    throw (IO.userError "the two-head shortcut did not return factor one")
  IO.println "PASS three positive tails and two heads returned exact factor one with zero feasibility tests"

private def twoTails : IO Unit := do
  let A : Adjacency 4 :=
    #v[#v[false,false,false,false],#v[false,false,false,false],
       #v[true,true,false,false],#v[false,false,true,false]]
  let w : Weights 4 :=
    #v[#v[zero,zero,zero,zero],#v[zero,zero,zero,zero],
       #v[half,quarter,zero,zero],#v[zero,zero,half,zero]]
  unless endpointCap A w == 2 && leastSupportedWithCalls A w == (1,0) do
    throw (IO.userError "the two-tail shortcut did not return factor one")
  IO.println "PASS two positive tails and three heads returned exact factor one with zero feasibility tests"

def main : IO Unit := do
  twoHeads
  twoTails
