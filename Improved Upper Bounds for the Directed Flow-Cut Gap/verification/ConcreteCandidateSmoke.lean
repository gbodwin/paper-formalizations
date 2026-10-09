import DirectedFlowCutGap.RetainedCandidateSolver

set_option synthInstance.maxSize 8192

open DirectedFlowCutGap EncodedCandidateCapacity RetainedCandidateSolver

private def disconnected : Input 2 where
  adjacency := #v[#v[false,false],#v[false,false]]
  removed := #v[false,false]

private def pathThree : Input 3 where
  adjacency := #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
  removed := #v[false,false,false]

#eval do
  let r := solve disconnected 0 1 1 (2^80)
  if r.numerators != [(0,0),(1,0)] then
    throw (IO.userError "wrong disconnected candidate output")
  if r.work > operationBound 2 1 then throw (IO.userError "complete candidate bound exceeded")
  IO.println s!"PASS generated dictionary, huge cap, retained backend and disconnected decode; work={r.work}"

#eval do
  let F := CandidateEnumeration.make 3 1
  let r := arrayRow F pathThree 0 2 1
  if r.1.toArray != #[0,1,0] then
    throw (IO.userError "nontrivial path optimizer did not retain the unique internal cut")
  if r.2 > EncodedCandidateOutput.operationBound 3 1+3^2+7*3+3 then
    throw (IO.userError "counted row materialization bound exceeded")
  IO.println s!"PASS positive-budget path optimization and counted natural-array output; row={r.1.toArray}, work={r.2}"

#eval do
  let D : Input 2 := { disconnected with removed := #v[true,true] }
  let r := solve D 0 1 1 (2^80)
  if r.numerators != [(0,1),(1,1)] then
    throw (IO.userError "zero-budget removed override failed")
  if r.work > operationBound 2 1 then throw (IO.userError "zero-budget bound exceeded")
  IO.println s!"PASS zero-budget retained pipeline; work={r.work}"
