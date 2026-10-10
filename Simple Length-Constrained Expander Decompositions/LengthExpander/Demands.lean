import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Finite directed integral demands from Definitions 2.2--2.4. -/
namespace LengthExpander
open Finset
variable {V : Type*} [Fintype V]

abbrev Demand (V : Type*) := V → V → ℕ
abbrev NodeWeight (V : Type*) := V → ℕ

def demandSize (D : Demand V) : ℕ := ∑ u, ∑ v, D u v

def weightSize (A : NodeWeight V) : ℕ := ∑ v, A v

def Respects (D : Demand V) (A : NodeWeight V) : Prop :=
  (∀ u, ∑ v, D u v ≤ A u) ∧ (∀ v, ∑ u, D u v ≤ A v)

theorem demandSize_le_weightSize {D : Demand V} {A : NodeWeight V}
    (hD : Respects D A) : demandSize D ≤ weightSize A := by
  exact sum_le_sum fun u _ => hD.1 u

theorem respects_zero (A : NodeWeight V) : Respects (fun _ _ => 0) A := by
  simp [Respects]

theorem respects_mono {D E : Demand V} {A : NodeWeight V}
    (h : ∀ u v, D u v ≤ E u v) (hE : Respects E A) : Respects D A := by
  constructor
  · intro u
    exact le_trans (sum_le_sum fun v _ => h u v) (hE.1 u)
  · intro v
    exact le_trans (sum_le_sum fun u _ => h u v) (hE.2 v)

theorem demand_entry_le {D : Demand V} {A : NodeWeight V}
    (hD : Respects D A) (u v : V) : D u v ≤ A u := by
  exact (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ v)).trans (hD.1 u)

/-- Lemma 5.2 in the correct inequality form, for a positive-volume witness.
The graph/length conditions on a sparse witness are not needed for this bound. -/
theorem sparse_cut_size_le {D : Demand V} {A : NodeWeight V}
    {cost φ : ℝ} (hφ : 0 ≤ φ) (hD : Respects D A)
    (hsparse : cost ≤ φ * (demandSize D : ℝ)) :
    cost ≤ φ * (weightSize A : ℝ) := by
  exact hsparse.trans (mul_le_mul_of_nonneg_left
    (by exact_mod_cast demandSize_le_weightSize hD) hφ)

/-- The correct aggregation used in Theorem 5.1 is a ratio of sums,
not the displayed sum of ratios. -/
theorem sum_cost_le {I : Type*} [Fintype I] (c v : I → ℝ) (φ : ℝ)
    (h : ∀ i, c i ≤ φ * v i) :
    (∑ i, c i) ≤ φ * ∑ i, v i := by
  calc
    (∑ i, c i) ≤ ∑ i, φ * v i := sum_le_sum fun i _ => h i
    _ = φ * ∑ i, v i := (mul_sum _ _ _).symm

theorem ratio_of_sums_le {I : Type*} [Fintype I] (c v : I → ℝ) (φ : ℝ)
    (hv : 0 < ∑ i, v i) (h : ∀ i, c i ≤ φ * v i) :
    (∑ i, c i) / (∑ i, v i) ≤ φ := by
  exact (div_le_iff₀ hv).2 (sum_cost_le c v φ h)

end LengthExpander
