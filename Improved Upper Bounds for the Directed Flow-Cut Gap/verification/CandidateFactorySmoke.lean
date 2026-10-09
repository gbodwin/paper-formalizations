import DirectedFlowCutGap.CandidateEnumeration

open DirectedFlowCutGap CandidateEnumeration

#eval do
  let F := make 0 3
  if F.base.enumeration.vertices.length != 0 || F.points.enumeration.vertices.length != 0 ||
      F.nodes.enumeration.vertices.length != 0 || F.network.enumeration.vertices != ([.inr false,.inr true] : List (Network 0 3)) then
    throw (IO.userError "empty factory had incorrect lists")
  if F.work != 6*3+127 then throw (IO.userError "empty factory cost mismatch")
  IO.println "PASS empty factory with positive level bound"

#eval do
  let F := make 3 2
  let labels := F.network.enumeration.vertices
  if labels.length != 56 then throw (IO.userError "wrong network cardinality")
  if labels.map networkIndex != List.range 56 then
    throw (IO.userError "network indices disagree with actual deterministic list positions")
  if labels != networkOrder 3 2 then throw (IO.userError "nested list order changed")
  if F.base.enumeration.vertices.map Fin.val != [0,1,2] then
    throw (IO.userError "base list is not ascending")
  if @Fintype.card (Network 3 2) F.network.dictionary != 56 then
    throw (IO.userError "retained dictionary has wrong cardinality")
  for p in labels do
    if (networkIndexWithCost p).1 != networkIndex p || (networkIndexWithCost p).2 > 15 then
      throw (IO.userError "counted index helper disagrees")
  IO.println s!"PASS nested product/sum order, retained dictionary, and all direct indices; work={F.work}"

#eval do
  for n in [1,2,3,4] do
    for L in [0,1,2,3] do
      let F := make n L
      if F.work != 120*n*(L+1)+155*n+6*L+127 then
        throw (IO.userError "factory recurrence charge mismatch")
      if F.work > 60*(6*n*(L+1)+3) then
        throw (IO.userError "factory linear-network bound exceeded")
      if F.network.enumeration.vertices.map networkIndex != List.range (6*n*(L+1)+2) then
        throw (IO.userError "index/list order mismatch in boundary sweep")
  IO.println "PASS exact factory charge and order for 16 nonempty boundary cases"
