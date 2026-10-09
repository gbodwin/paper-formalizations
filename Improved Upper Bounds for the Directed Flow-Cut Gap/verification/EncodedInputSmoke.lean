import DirectedFlowCutGap.EncodedRoundingInput

open DirectedFlowCutGap RetainedGridState EncodedIntegerShortestPaths EncodedRoundingInput

private def chain : PairFlags 3 := Vector.ofFn fun u => Vector.ofFn fun v =>
  decide ((u.val,v.val)=(0,1) ∨ (u.val,v.val)=(1,2))

#eval do
  let E := IntegralNetworkFlow.ResidualSearch.Enumeration.fin 3
  let a : Row 3 := #v[0,1,0]
  for s in List.finRange 3 do
    for t in List.finRange 3 do
      let r := distance E chain a s t
      let reference := IntegerLevelCuts.vertexDistance E (graph chain) (fun v => a[v.val]) s t
      if r.1 != reference.1 then throw (IO.userError "distance refinement mismatch")
      if r.2 > distanceBound 3 then throw (IO.userError "distance word bound exceeded")
  let d := distance E chain a 0 2
  if d.1 != (1 : WithTop Nat) then throw (IO.userError "endpoint-excluding distance wrong")
  let disconnected := distance E chain a 2 0
  if disconnected.1 != none then throw (IO.userError "disconnected distance lost infinity")
  let zero := distance E chain (#v[0,0,0] : Row 3) 0 2
  if zero.1 != (0 : WithTop Nat) then throw (IO.userError "zero-weight distance wrong")
  let cut := cutFlags E chain a 0 0
  if cut.1 != (#v[false,true,false] : Flags 3) then throw (IO.userError "midpoint flags wrong")
  if cut.2 > cutBound 3 then throw (IO.userError "cut word bound exceeded")
  let m := demandMask E chain 1
  let expected : PairFlags 3 := #v[#v[false,false,true],#v[true,false,false],#v[true,true,false]]
  if m.1 != expected then throw (IO.userError "original demand mask wrong")
  if m.2 > maskBound 3 then throw (IO.userError "mask word bound exceeded")
  let huge := demandMask E chain (2^30)
  if huge.2 != m.2 then throw (IO.userError "binary threshold incorrectly controls a loop")
  if flag huge.1 (0,2) || !(flag huge.1 (2,0)) then throw (IO.userError "huge threshold semantics wrong")
  IO.println s!"PASS encoded chain, zero weights, endpoints, infinity, midpoint, mask and huge binary threshold; distance={d.2}, mask={m.2}, cut={cut.2}"

#eval do
  let E := IntegralNetworkFlow.ResidualSearch.Enumeration.fin 0
  let adjacency : PairFlags 0 := #v[]
  let m := demandMask E adjacency 1000000000
  if m.1 != (#v[] : PairFlags 0) then throw (IO.userError "empty mask wrong")
  if m.2 > maskBound 0 then throw (IO.userError "empty mask charge exceeded")
  IO.println s!"PASS empty mask; work={m.2}"
