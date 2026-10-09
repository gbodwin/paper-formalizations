import DirectedFlowCutGap.CountedTabulatedFlow

open DirectedFlowCutGap IntegralNetworkFlow IntegralNetworkFlow.Tabulated

private def testCapacity (u v : Fin 4) : ℕ :=
  if (u,v) ∈ ([(0,1),(0,2),(1,2),(1,3),(2,3)] : List (Fin 4 × Fin 4)) then 1 else 0

private def reverseEnumeration : ResidualSearch.Enumeration (Fin 4) where
  vertices := [3,2,1,0]
  nodup := by decide
  complete := by intro v; fin_cases v <;> decide

#eval do
  let cs := FlowTable.dense reverseEnumeration fun u v => (testCapacity u v : Int)
  let c := CountedFlow.capacityOf cs
  let initial := FlowTable.materialize reverseEnumeration (Flow.zero c 0 3)
  let first := CountedFlow.runWithCost cs reverseEnumeration initial 1
  let second := CountedFlow.runWithCost cs reverseEnumeration initial 2
  if (read (1,2) first.1.cells).1 != 1 then throw (IO.userError "crossing edge not used")
  if (read (1,2) second.1.cells).1 != 0 then throw (IO.userError "reverse cancellation not executed")
  if second.1.asFlow.value != 2 then throw (IO.userError "wrong maximum flow")
  let cut := CountedFlow.solve cs reverseEnumeration 0 3 2
  if !(0 ∈ cut.asSet) || (3 ∈ cut.asSet) then throw (IO.userError "nonseparating final cut")
  if cut.work > 256*(2+1)*(4+1)^5 then throw (IO.userError "dense polynomial charge exceeded")
  IO.println s!"PASS counted two-table flow and reverse cancellation; work={cut.work}"

#eval do
  let E := ResidualSearch.Enumeration.fin 3
  let cs := FlowTable.dense E fun _ _ => (0 : Int)
  let r := CountedFlow.solve cs E 0 2 0
  if r.vertices != [0,1] then throw (IO.userError "zero-budget/disconnected final cut is wrong")
  if r.work > 256*(0+1)*(3+1)^5 then throw (IO.userError "zero-budget charge exceeded")
  IO.println s!"PASS zero-budget disconnected final search; work={r.work}"

#eval do
  let E := ResidualSearch.Enumeration.fin 2
  let cs := FlowTable.dense E fun u v => if u=0 ∧ v=1 then (3 : Int) else 0
  let r := CountedFlow.solve cs E 0 1 3
  if r.vertices != [0] then throw (IO.userError "three-unit saturated cut is wrong")
  if r.work > 256*(3+1)*(2+1)^5 then throw (IO.userError "three-unit charge exceeded")
  IO.println s!"PASS repeated integer augmentation; work={r.work}"
