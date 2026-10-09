import DirectedFlowCutGap.FractionalCoverGraphOracle
import DirectedFlowCutGap.FractionalCoverInputEncoding
open DirectedFlowCutGap
open FractionalCover FractionalCoverWalkOracle FractionalCoverPathOracle FractionalCoverGraphOracle
open IntegralNetworkFlow

namespace FractionalCoverOracleSmoke

def cycleGraph : Digraph (Fin 4) where
  Adj u v := (u,v) ∈ ([(0,1),(1,1),(1,2),(2,1),(2,3),(0,3)] : List (Fin 4 × Fin 4))
instance : DecidableRel cycleGraph.Adj := fun u v => inferInstanceAs
  (Decidable ((u,v) ∈ ([(0,1),(1,1),(1,2),(2,1),(2,3),(0,3)] : List (Fin 4 × Fin 4))))

def edgeCosts (e : Fin 4 × Fin 4) : ℚ :=
  if e=(0,1) then 5 else if e=(2,3) then 1 else if e=(0,3) then 10 else 0

#eval do
  let E := ResidualSearch.Enumeration.fin 4
  let walk := minimize E cycleGraph edgeCosts 0 3
  let answer := shortest E cycleGraph edgeCosts 0 3
  match walk.1, answer.1 with
  | some w, some p =>
      if w.edges.length != 4 then throw (IO.userError "bounded witness did not retain expected zero loop")
      if p.edges.length != 3 then throw (IO.userError "recovery did not erase the zero loop")
      if p.cost != 6 then throw (IO.userError "wrong recovered shortest-path cost")
      if p.edges != [(0,1),(1,2),(2,3)] then throw (IO.userError "wrong retained minimum-path edge list")
      IO.println s!"PASS: actual bounded walk of {w.edges.length} edges recovered as {p.edges.length}-edge minimum path; cost={p.cost}; charged work={answer.2}"
  | _, _ => throw (IO.userError "reachable minimum path was not returned")
  if (shortest E cycleGraph edgeCosts 3 0).1.isSome then
    throw (IO.userError "unreachable source returned a path")
  match (shortest E cycleGraph edgeCosts 1 1).1 with
  | some p =>
      if p.edges != [] || p.cost != 0 then throw (IO.userError "diagonal zero path is wrong")
  | none => throw (IO.userError "diagonal path omitted")
  match (shortest E cycleGraph (fun e => edgeCosts e / 7) 0 3).1 with
  | some p =>
      if p.cost != 6/7 then throw (IO.userError "fractional shortest-path cost is wrong")
  | none => throw (IO.userError "fractional instance omitted")
  IO.println "PASS: unreachable, diagonal, and subunit rational-cost shortest-path cases"

def matrixInput : FractionalCoverGraphOracle.Input 4 where
  adjacency := #v[#v[false,true,true,false],#v[false,false,false,true],
    #v[false,false,false,true],#v[false,false,false,false]]
  demands := [(0,3)]
  costs := #v[(1 : ℚ),1,4,1]

def coverGraph : Digraph (Fin 4) := matrixInput.graph
instance : DecidableRel coverGraph.Adj := fun u v => inferInstanceAs
  (Decidable (matrixInput.adjacency[u.val][v.val] = true))

def demands : List (Fin 4 × Fin 4) := matrixInput.demands
def resourceCosts : Row 4 := matrixInput.costs

def seed : SimplePath coverGraph 0 3 where
  edgeLength := 2
  vertex := ![0,1,3]
  source_eq := rfl
  target_eq := rfl
  injective := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  adjacent := by intro i; fin_cases i <;> decide

theorem domain : Domain coverGraph demands := by
  constructor
  · exact ⟨(0,3),by simp [demands,matrixInput],⟨seed⟩⟩
  · intro d hd p
    simp only [demands,matrixInput,List.mem_singleton] at hd
    subst d
    exact internal_nonempty_of_nonadjacent p (by decide) (by decide)

theorem costs_positive : ∀ i, 0 < value resourceCosts i := by
  intro i
  fin_cases i <;> norm_num [resourceCosts,matrixInput,value]

example : Feasible (columns coverGraph demands)
    (solveGraph coverGraph demands resourceCosts (by decide)).best :=
  solveGraph_feasible coverGraph demands resourceCosts (by decide) costs_positive domain

#eval do
  let out := matrixInput.solve (by decide)
  if !(1 ≤ value out.best 1 ∧ 1 ≤ value out.best 2) then
    throw (IO.userError "actual graph output did not cover both internally disjoint demand paths")
  if !(objective resourceCosts out.best ≤ 15) then
    throw (IO.userError "graph cover exceeded three times the exact five-unit comparator")
  if !(1 ≤ objective resourceCosts out.weights) then throw (IO.userError "graph solver did not stop")
  IO.println s!"PASS: concrete graph oracle and cover recurrence; updates={out.events.length}; output cost={objective resourceCosts out.best}; cover={reprStr out.best}"

end FractionalCoverOracleSmoke
