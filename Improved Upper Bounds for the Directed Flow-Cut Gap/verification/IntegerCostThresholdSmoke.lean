import DirectedFlowCutGap.IntegerCostThreshold
open DirectedFlowCutGap.IntegerCostThreshold
#eval do
  unless factor 8 2 == 9 do throw (IO.userError "integer square-root factor")
  unless factor 7 2 == 7 do throw (IO.userError "double-floor factor")
  unless factor 3 7 == 1 do throw (IO.userError "large-threshold factor")
  unless cutoff 3 1 > 0 do throw (IO.userError "computed cutoff positivity")
  IO.println "PASS actual integer factor and cutoff evaluation"
