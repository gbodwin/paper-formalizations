import DirectedFlowCutGap.ClosureRuntime

open DirectedFlowCutGap
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated

private def testCapacity (u v : Fin 4) : ℕ :=
  if (u,v) ∈ ([(0,1),(0,2),(1,2),(1,3),(2,3)] : List (Fin 4 × Fin 4)) then 1 else 0

private def reverseEnumeration : ResidualSearch.Enumeration (Fin 4) where
  vertices := [3,2,1,0]
  nodup := by decide
  complete := by intro v; fin_cases v <;> decide

#eval do
  let initial := FlowTable.materialize reverseEnumeration (Flow.zero testCapacity 0 3)
  let first := FlowTable.runWithCost reverseEnumeration initial 1
  let second := FlowTable.runWithCost reverseEnumeration initial 2
  if (read (1,2) first.1.cells).1 != 1 then
    throw (IO.userError "first path must use the crossing edge")
  if (read (1,2) second.1.cells).1 != 0 then
    throw (IO.userError "second augmentation must cancel the crossing edge")
  if second.1.asFlow.value != 2 then throw (IO.userError "maximum flow must be two")
  if second.1.cells.length != 16 then throw (IO.userError "dense table length changed")
  let cut := ClosureRuntime.finalCutWithCost reverseEnumeration second.1.asFlow
  if !(0 ∈ cut.1) || (3 ∈ cut.1) then throw (IO.userError "final cut does not separate")
  if second.2 > 2 * FlowTable.stepCharge 4 16 then throw (IO.userError "table charge exceeded")
  IO.println s!"PASS retained flow, reverse cancellation, final cut; charged work={second.2}, cut work={cut.2}"

private def testProblem : MinimumClosureProblem.Problem (Fin 3) where
  required := {0}
  forbidden := {2}
  arcs := {(0,1)}
  cost := fun a => if a = 1 then -2 else if a = 2 then -3 else 0

private def closureEnumeration : ResidualSearch.Enumeration (MinimumClosureCut.Vertex (Fin 3)) where
  vertices := [.inl 0,.inl 1,.inl 2,.inr false,.inr true]
  nodup := by decide
  complete := by
    intro v
    cases v with
    | inl v => fin_cases v <;> simp
    | inr b => cases b <;> simp

#eval do
  let r := ClosureRuntime.solve testProblem closureEnumeration
  if r.1 != ({0,1} : Finset (Fin 3)) then throw (IO.userError "wrong retained closure")
  if testProblem.objective r.1 != -2 then throw (IO.userError "wrong signed closure cost")
  if r.2 > ClosureRuntime.closureCharge 5 5 then throw (IO.userError "closure charge exceeded")
  IO.println s!"PASS signed closure, required/forbidden vertices, capacity retention; charged work={r.2}"
