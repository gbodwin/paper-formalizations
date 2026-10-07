import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.List.Chain
import Mathlib.Tactic

/-!
# A counterexample to the *stated construction* in Theorem 5

This does not refute the existential statement of Theorem 5. It refutes the
claim that the displayed modular construction with weights sqrt(1+a^2)
always has the designated paths as shortest paths. The graph is undirected.
-/
namespace LinearDistancePreservers.WeightedConstruction

abbrev Vertex := Fin 3 × Fin 30

/-- The edges in the paper's modular construction for n=30, ell=3, x=10. -/
def Forward (u v : Vertex) : Prop :=
  u.1.val + 1 = v.1.val ∧ ∃ a : Fin 10, v.2.val = (u.2.val + a.val) % 30

instance (u v : Vertex) : Decidable (Forward u v) := inferInstanceAs
  (Decidable (u.1.val + 1 = v.1.val ∧ ∃ a : Fin 10, v.2.val = (u.2.val + a.val) % 30))

def Adj (u v : Vertex) : Prop := Forward u v ∨ Forward v u
instance (u v : Vertex) : Decidable (Adj u v) := inferInstanceAs
  (Decidable (Forward u v ∨ Forward v u))

theorem adj_symm {u v : Vertex} : Adj u v → Adj v u := Or.symm

/-- Recover the slope from the lower-layer endpoint, including wraparound. -/
def slope (u v : Vertex) : ℕ :=
  if u.1 < v.1 then (v.2.val + 30 - u.2.val) % 30
  else (u.2.val + 30 - v.2.val) % 30

noncomputable def weight (u v : Vertex) : ℝ :=
  Real.sqrt (1 + (slope u v : ℝ)^2)

noncomputable def cost : List Vertex → ℝ
  | [] => 0
  | [_] => 0
  | u :: v :: rest => weight u v + cost (v :: rest)

def Valid (p : List Vertex) : Prop := p.IsChain Adj

noncomputable def IsShortest (p : List Vertex) : Prop :=
  Valid p ∧ ∀ q : List Vertex, Valid q → q.head? = p.head? →
    q.getLast? = p.getLast? → cost p ≤ cost q

def designated : List Vertex := [(0,0), (1,9), (2,18)]
def competitor : List Vertex := [(0,0), (1,0), (0,24), (1,24), (0,18), (1,18), (2,18)]

/-- All parameters satisfy the paper's constraints. -/
theorem admissible_parameters : 3 ≤ 30 ∧ 10 ≤ 30 / 3 := by decide

theorem designated_valid : Valid designated := by
  unfold Valid designated
  decide

theorem competitor_valid : Valid competitor := by
  unfold Valid competitor
  decide

theorem competitor_simple : competitor.Nodup := by decide

theorem same_endpoints : competitor.head? = designated.head? ∧
    competitor.getLast? = designated.getLast? := by decide

theorem designated_cost : cost designated = 2 * Real.sqrt 82 := by
  norm_num [designated,cost,weight,slope]
  ring

theorem competitor_cost : cost competitor = 4 + 2 * Real.sqrt 37 := by
  norm_num [competitor,cost,weight,slope]
  ring

/-- Exact radical comparison; no floating-point arithmetic or native_decide. -/
theorem competitor_strictly_shorter : cost competitor < cost designated := by
  rw [competitor_cost,designated_cost]
  have hs37 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 37)
  have hs82 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 82)
  have hn37 := Real.sqrt_nonneg (37:ℝ)
  have hn82 := Real.sqrt_nonneg (82:ℝ)
  have h37 : Real.sqrt 37 < 7 := by nlinarith
  have h82 : 9 < Real.sqrt 82 := by nlinarith
  linarith

/-- The designated constant-slope route is not shortest in the stated graph. -/
theorem designated_not_shortest : ¬ IsShortest designated := by
  intro h
  exact (not_le.mpr competitor_strictly_shorter)
    (h.2 competitor competitor_valid same_endpoints.1 same_endpoints.2)

end LinearDistancePreservers.WeightedConstruction
