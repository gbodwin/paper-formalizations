import DirectedFlowCutGap.RationalInstanceEdgeFactor

open DirectedFlowCutGap
open RationalInstanceEdgeFactor (endpointCap leastSupportedWithCalls)

def main : IO Unit := do
  let z := BinaryRational.zero
  let one := BinaryRational.one
  let half : BinaryRational.Fraction := ⟨[true],[false,true],by decide⟩
  let triangle : BinaryFractionalWalkOracle.Adjacency 3 :=
    #v[#v[false,true,false],#v[false,false,true],#v[true,false,false]]
  let halves : RationalEdgeThresholds.Weights 3 :=
    #v[#v[z,half,z],#v[z,z,half],#v[half,z,z]]
  unless endpointCap triangle halves == 3 && leastSupportedWithCalls triangle halves == (2,2) do
    throw (IO.userError "bisection changed the exact triangle factor")
  IO.println "PASS the directed triangle found exact factor two in two feasibility tests"
  let fan : BinaryFractionalWalkOracle.Adjacency 4 :=
    #v[#v[false,true,true,true],#v[false,false,false,false],#v[false,false,false,false],#v[false,false,false,true]]
  let unitLengths : RationalEdgeThresholds.Weights 4 :=
    #v[#v[z,one,one,one],#v[z,z,z,z],#v[one,z,z,z],#v[z,z,z,one]]
  unless endpointCap fan unitLengths == 1 && leastSupportedWithCalls fan unitLengths == (1,0) do
    throw (IO.userError "nonedges or loops were used in the path endpoint bound")
  IO.println "PASS the four-vertex source fan used a one-endpoint cap and no feasibility tests"
  let loops : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[true,false],#v[false,true]]
  let loopLengths : RationalEdgeThresholds.Weights 2 := #v[#v[one,z],#v[z,one]]
  unless endpointCap loops loopLengths == 0 && leastSupportedWithCalls loops loopLengths == (0,0) do
    throw (IO.userError "the loop-only graph used a nonzero endpoint factor")
  IO.println "PASS the loop-only graph returned zero before any feasibility test"
  let short : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
  let subunit : RationalEdgeThresholds.Weights 2 := #v[#v[z,half],#v[z,z]]
  unless endpointCap short subunit == 1 && leastSupportedWithCalls short subunit == (0,0) do
    throw (IO.userError "the empty-cut test incorrectly found a reachable threshold pair")
  IO.println "PASS the subunit path had a positive endpoint cap and returned factor zero without testing feasibility"
