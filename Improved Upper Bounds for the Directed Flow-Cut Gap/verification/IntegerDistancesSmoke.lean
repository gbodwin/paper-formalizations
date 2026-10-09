import DirectedFlowCutGap.IntegerLevelCuts

open DirectedFlowCutGap
open IntegerShortestPaths

def chain : Digraph (Fin 4) where
  Adj u v := u.val + 1 = v.val
instance : DecidableRel chain.Adj := fun _ _ => inferInstanceAs (Decidable (_ + 1 = _))

def diamond : Digraph (Fin 4) where
  Adj u v := (u.val = 0 ∧ (v.val = 1 ∨ v.val = 2)) ∨
    ((u.val = 1 ∨ u.val = 2) ∧ v.val = 3) ∨ u = v
instance : DecidableRel diamond.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def edgeCost (e : Fin 4 × Fin 4) : ℕ :=
  if e = (0,1) then 9 else if e = (1,3) then 1 else if e = (0,2) then 1
  else if e = (2,3) then 2 else 0

def numerator : Fin 4 → ℕ := ![7,0,5,11]

def check : IO Unit := do
  let E := IntegralNetworkFlow.ResidualSearch.Enumeration.fin 4
  let c := distance E chain (fun e => e.1.val+1) 0 3
  unless c == ((6 : WithTop ℕ),129) do throw (IO.userError "chain distance/count")
  let z := distance E diamond (fun _ => 0) 0 3
  unless z.1 == (0 : WithTop ℕ) do throw (IO.userError "zero distance")
  let d := distance E diamond edgeCost 0 3
  unless d.1 == (3 : WithTop ℕ) do throw (IO.userError "diamond distance")
  let u := IntegerLevelCuts.vertexDistance E chain numerator 3 0
  unless u.1 == (⊤ : WithTop ℕ) do throw (IO.userError "disconnected distance")
  let self := IntegerLevelCuts.vertexDistance E chain numerator 3 3
  unless self.1 == (0 : WithTop ℕ) do throw (IO.userError "self distance")
  let v := IntegerLevelCuts.vertexDistance E chain numerator 0 3
  unless v.1 == (5 : WithTop ℕ) do throw (IO.userError "endpoint distance")
  let a := IntegerLevelCuts.cut E chain numerator 0 4
  unless a == (({0,2} : Finset (Fin 4)),536) do
    throw (IO.userError "midpoint cell 4/count")
  let b := IntegerLevelCuts.cut E chain numerator 0 5
  unless b.1 == ({0,3} : Finset (Fin 4)) do throw (IO.userError "midpoint cell 5")
  let empty := IntegerLevelCuts.cutScan E chain numerator 0 0 []
  unless empty == ([],0) do throw (IO.userError "empty traversal")
  IO.println "PASS executed shortest paths: cheaper alternative, zero-cost loops, disconnected infinity, self, excluded endpoints, exact counter 129, midpoint cuts, exact cut count 536, empty traversal"

#eval check
