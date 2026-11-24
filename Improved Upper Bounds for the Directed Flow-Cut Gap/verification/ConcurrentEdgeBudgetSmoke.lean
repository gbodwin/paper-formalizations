import DirectedFlowCutGap.ConcurrentEdgeBudgetRound

open DirectedFlowCutGap
open scoped NNRat
open BinaryRational (zero one)

private def forward : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
private def opposed : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[true,false]]
private def prices : RationalEdgeThresholds.Weights 2 := #v[#v[zero,one],#v[one,zero]]
private def free : RationalEdgeThresholds.Weights 2 := #v[#v[zero,zero],#v[zero,zero]]
private def singleDemand : Vector (Fin 2 × Fin 2) 1 := #v[(0,1)]
private def twoDemands : Vector (Fin 2 × Fin 2) 2 := #v[(0,1),(1,0)]
private def tape := [true,false,true]
private theorem nonemptyGraph : 0 < 2 := by decide

def main : IO Unit := do
  let some small := ConcurrentEdgeBudgetSelection.choose nonemptyGraph forward prices singleDemand |
    throw (IO.userError "the generated budgets produced no mass plan")
  match small.mode with
  | .size => throw (IO.userError "one original arc should select the mass scale")
  | .mass => pure ()
  let some (.cut cut unread) :=
    ConcurrentEdgeBudgetRound.run nonemptyGraph forward prices singleDemand 0 tape |
    throw (IO.userError "the budget-selected mass round returned no cut")
  unless cut.toList.map Vector.toList == [[false,true],[false,false]] && unread == tape do
    throw (IO.userError "budget-selected mass rounding changed the original cut or unread bits")
  IO.println s!"PASS generated budgets selected the mass scale with score {(small.receipt : ℚ)} and original arc, unread {unread}"
  let some large := ConcurrentEdgeBudgetSelection.choose nonemptyGraph opposed prices twoDemands |
    throw (IO.userError "the generated budgets produced no size plan")
  match large.mode with
  | .mass => throw (IO.userError "two opposed demands should select the size scale")
  | .size => pure ()
  let some (.cut selected suffix) :=
    ConcurrentEdgeBudgetRound.run nonemptyGraph opposed prices twoDemands 0 tape |
    throw (IO.userError "the budget-selected size round returned no cut")
  unless !selected[0][0] && !selected[1][1] && (selected[0][1] || selected[1][0]) && suffix == tape do
    throw (IO.userError "budget-selected size rounding changed the original support or unread bits")
  IO.println s!"PASS generated budgets selected the size scale with score {(large.receipt : ℚ)} and original cut {selected.toList.map Vector.toList}"
  let some (.cut freeCut freeRest) :=
    ConcurrentEdgeBudgetRound.run nonemptyGraph forward free singleDemand 0 tape |
    throw (IO.userError "the zero-cost branch returned no cut")
  unless freeCut == cut && freeRest == tape do
    throw (IO.userError "the zero-cost branch changed the original arc or unread bits")
  IO.println "PASS free-arc branch returned the original zero-cost cut with the entire tape"
