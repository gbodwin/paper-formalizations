import DirectedFlowCutGap.EncodedEpochParameters
import DirectedFlowCutGap.EncodedDyadicRoot
open DirectedFlowCutGap

#eval do
  let mut logs := 0
  for b in [0,1,2,3,4,17] do
    for x in List.range 257 do
      let out := EncodedEpochParameters.floorLog b x x
      unless out.1 == Nat.log b x && out.2 ≤ 12*x+6 do
        throw (IO.userError "bounded logarithm value/charge failed")
      logs := logs+1
  for n in List.range 129 ++ [2^30,2^128+1] do
    let out := EncodedEpochParameters.compute n
    unless out.restart == IntegerEpochParameters.restart n &&
        out.fuel == IntegerEpochParameters.fuel n &&
        out.cap == IntegerEpochParameters.cap n &&
        out.work ≤ EncodedEpochParameters.operationBound n do
      throw (IO.userError "epoch parameter value/charge failed")
  let mut roots := 0
  for n in List.range 65 do
    for L in List.range (n+1) do
      let out := EncodedDyadicRoot.compute n L
      unless out.work ≤ EncodedDyadicRoot.operationBound n L do
        throw (IO.userError "root work bound failed")
      if 0<L then
        unless n ≤ L*out.upper^2 && L*out.upper^2 ≤ 9*n do
          throw (IO.userError "root squared approximation failed")
        roots := roots+1
  for n in [2^30,2^128+1] do
    let out := EncodedDyadicRoot.compute n 1
    unless n ≤ out.upper^2 && out.upper^2 ≤ 9*n &&
        out.work ≤ EncodedDyadicRoot.operationBound n 1 do
      throw (IO.userError "huge binary root case failed")
  IO.println s!"PASS {logs} logarithms, 131 exact epoch parameter cases, {roots} positive root cases, zero denominators, and huge binary inputs"
