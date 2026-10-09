import DirectedFlowCutGap.EncodedCandidateOutput

set_option synthInstance.maxSize 8192

open DirectedFlowCutGap IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open CandidateGridOptimizer CandidateThresholdClosure EncodedCandidateCapacity

private def nodes : ResidualSearch.Enumeration (Node (Point (Fin 2)) 1) where
  vertices := [
    ((TerminalPorts.core 0,false),0),
    ((TerminalPorts.core 0,false),1),
    ((TerminalPorts.core 0,true),0),
    ((TerminalPorts.core 0,true),1),
    ((TerminalPorts.core 1,false),0),
    ((TerminalPorts.core 1,false),1),
    ((TerminalPorts.core 1,true),0),
    ((TerminalPorts.core 1,true),1),
    ((TerminalPorts.source 0,false),0),
    ((TerminalPorts.source 0,false),1),
    ((TerminalPorts.source 0,true),0),
    ((TerminalPorts.source 0,true),1),
    ((TerminalPorts.source 1,false),0),
    ((TerminalPorts.source 1,false),1),
    ((TerminalPorts.source 1,true),0),
    ((TerminalPorts.source 1,true),1),
    ((TerminalPorts.sink 0,false),0),
    ((TerminalPorts.sink 0,false),1),
    ((TerminalPorts.sink 0,true),0),
    ((TerminalPorts.sink 0,true),1),
    ((TerminalPorts.sink 1,false),0),
    ((TerminalPorts.sink 1,false),1),
    ((TerminalPorts.sink 1,true),0),
    ((TerminalPorts.sink 1,true),1)]
  nodup := by decide
  complete := by
    intro a
    rcases a with ⟨⟨v,b⟩,l⟩
    rcases v with v | v
    · fin_cases v <;> cases b <;> fin_cases l <;> simp
    · cases v with
      | inl v => fin_cases v <;> cases b <;> fin_cases l <;> simp
      | inr v => fin_cases v <;> cases b <;> fin_cases l <;> simp

private def vertices : ResidualSearch.Enumeration (MinimumClosureCut.Vertex (Node (Point (Fin 2)) 1)) where
  vertices := nodes.vertices.map Sum.inl ++ [.inr false,.inr true]
  nodup := by decide
  complete := by
    intro v
    cases v with
    | inl a => simp [nodes.complete a]
    | inr b => cases b <;> simp

private def disconnected : Input 2 where
  adjacency := #v[#v[false,false],#v[false,false]]
  removed := #v[false,false]

#eval do
  let huge := 2^80
  let c := disconnected.construct 0 1 1 huge nodes vertices
  if c.budget != 4 then throw (IO.userError "wrong retained budget")
  if c.cells.length != 26^2 then throw (IO.userError "wrong dense capacity-table length")
  if c.work > 90*27^2 then throw (IO.userError "construction charge exceeded")
  if c.cells.any (fun e => decide (e.2 < 0) || decide (9 < e.2)) then
    throw (IO.userError "capacity lost its budget bound for huge B")
  let d := disconnected.construct 0 1 1 1 nodes vertices
  if c.cells != d.cells then throw (IO.userError "huge B changed capped threshold capacities")
  IO.println s!"PASS retained construction and huge-B capacity clipping; cells={c.cells.length}, work={c.work}"

#eval do
  let r := EncodedCandidateOutput.solve disconnected 0 1 1 1 nodes vertices
    (ResidualSearch.Enumeration.fin 2)
  if r.numerators != [(0,0),(1,0)] then throw (IO.userError "wrong disconnected numerators")
  if r.work > EncodedCandidateOutput.operationBound 2 1 then
    throw (IO.userError "whole-program operation bound exceeded")
  IO.println s!"PASS one retained solve and decoded disconnected numerators; work={r.work}"

#eval do
  let D : Input 2 := { disconnected with removed := #v[true,true] }
  let r := EncodedCandidateOutput.solve D 0 1 1 (2^80) nodes vertices
    (ResidualSearch.Enumeration.fin 2)
  if r.numerators != [(0,1),(1,1)] then throw (IO.userError "removed numerator override failed")
  if r.work > EncodedCandidateOutput.operationBound 2 1 then
    throw (IO.userError "zero-budget complete pipeline exceeded bound")
  IO.println s!"PASS zero-budget core extraction and removed-vertex override; work={r.work}"

#eval do
  let D : Input 2 :=
    { adjacency := #v[#v[true,false],#v[true,true]], removed := #v[true,false] }
  for u in vertices.vertices do
    for v in vertices.vertices do
      let r := D.capacityWithCost 0 1 1 (2^80) 7 u v
      if r.1 != D.directCapacity 0 1 1 (2^80) 7 u v then
        throw (IO.userError "concrete helper disagreed with direct threshold predicate")
      if r.2 > 68 then throw (IO.userError "straight-line capacity charge exceeded")
  IO.println "PASS all 676 typed arc cases with self edges, mixed removal, and huge cap"
