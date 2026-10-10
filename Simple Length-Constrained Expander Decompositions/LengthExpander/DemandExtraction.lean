import LengthExpander.Demands
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega

/-! A support-preserving integral extraction with a factor-two volume bound.

The fractional demand need not have integral entries. We maximize the size of
an integral demand on its support, show that every supported pair has a saturated
endpoint, and charge fractional mass to saturated rows and columns. No entrywise
inequality between the extracted demand and the fractional demand is asserted.
-/
namespace LengthExpander
open Finset
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

/-- An integral demand with largest total size among the feasible demands on a
specified relation. The search is bounded by the sum of the integral budgets. -/
theorem exists_maximal_supported_demand (A : NodeWeight V) (S : V → V → Prop) :
    ∃ D : Demand V, Respects D A ∧ (∀ u v, 0 < D u v → S u v) ∧
      ∀ E : Demand V, Respects E A → (∀ u v, 0 < E u v → S u v) →
        demandSize E ≤ demandSize D := by
  classical
  let P : ℕ → Prop := fun n => ∃ D : Demand V,
    Respects D A ∧ (∀ u v, 0 < D u v → S u v) ∧ demandSize D = n
  have hzero : P 0 := by
    refine ⟨fun _ _ => 0, respects_zero A, ?_, ?_⟩
    · intro u v h
      simp at h
    · simp [demandSize]
  obtain ⟨D, hD, hS, hsize⟩ :=
    Nat.findGreatest_spec (P := P) (Nat.zero_le (weightSize A)) hzero
  refine ⟨D, hD, hS, ?_⟩
  intro E hE hES
  rw [hsize]
  exact Nat.le_findGreatest (demandSize_le_weightSize hE) ⟨E, hE, hES, rfl⟩

/-- Add one unit to a single ordered pair. -/
noncomputable def incrementDemand (D : Demand V) (u v : V) : Demand V := by
  classical
  exact fun x y => D x y + if x = u ∧ y = v then 1 else 0

@[simp] theorem incrementDemand_row (D : Demand V) (u v x : V) :
    (∑ y, incrementDemand D u v x y) = (∑ y, D x y) + if x = u then 1 else 0 := by
  classical
  by_cases hx : x = u <;> simp [incrementDemand, sum_add_distrib, hx]

@[simp] theorem incrementDemand_column (D : Demand V) (u v y : V) :
    (∑ x, incrementDemand D u v x y) = (∑ x, D x y) + if y = v then 1 else 0 := by
  classical
  by_cases hy : y = v <;> simp [incrementDemand, sum_add_distrib, hy]

@[simp] theorem incrementDemand_size (D : Demand V) (u v : V) :
    demandSize (incrementDemand D u v) = demandSize D + 1 := by
  classical
  simp [demandSize, sum_add_distrib]

/-- Every allowed ordered pair has a saturated row or a saturated column in a
maximum supported integral demand. This also covers zero budgets and empty V. -/
theorem exists_saturated_supported_demand (A : NodeWeight V) (S : V → V → Prop) :
    ∃ D : Demand V, Respects D A ∧ (∀ u v, 0 < D u v → S u v) ∧
      ∀ u v, S u v → (∑ y, D u y) = A u ∨ (∑ x, D x v) = A v := by
  classical
  obtain ⟨D, hD, hS, hmax⟩ := exists_maximal_supported_demand A S
  refine ⟨D, hD, hS, ?_⟩
  intro u v huv
  by_cases hr : (∑ y, D u y) = A u
  · exact Or.inl hr
  by_cases hc : (∑ x, D x v) = A v
  · exact Or.inr hc
  have hr' : (∑ y, D u y) + 1 ≤ A u := by
    have := hD.1 u
    omega
  have hc' : (∑ x, D x v) + 1 ≤ A v := by
    have := hD.2 v
    omega
  have hinc : Respects (incrementDemand D u v) A := by
    constructor
    · intro x
      rw [incrementDemand_row]
      by_cases hx : x = u
      · subst x
        simpa using hr'
      · simpa [hx] using hD.1 x
    · intro y
      rw [incrementDemand_column]
      by_cases hy : y = v
      · subst y
        simpa using hc'
      · simpa [hy] using hD.2 y
  have hincS : ∀ x y, 0 < incrementDemand D u v x y → S x y := by
    intro x y hxy
    by_cases hpair : x = u ∧ y = v
    · rcases hpair with ⟨rfl, rfl⟩
      exact huv
    · apply hS x y
      simpa [incrementDemand, hpair] using hxy
  have hbad := hmax (incrementDemand D u v) hinc hincS
  rw [incrementDemand_size] at hbad
  omega

/-- If every positive fractional entry has a saturated integral row or column,
charging to those rows and columns loses at most a factor of two. -/
theorem fractional_mass_le_twice_of_saturated
    (F : V → V → ℝ) (A : NodeWeight V) (D : Demand V)
    (hF : ∀ u v, 0 ≤ F u v)
    (hrow : ∀ u, (∑ v, F u v) ≤ (A u : ℝ))
    (hcol : ∀ v, (∑ u, F u v) ≤ (A v : ℝ))
    (hsat : ∀ u v, 0 < F u v →
      (∑ y, D u y) = A u ∨ (∑ x, D x v) = A v) :
    (∑ u, ∑ v, F u v) ≤ 2 * (demandSize D : ℝ) := by
  classical
  let R : V → Prop := fun u => (∑ v, D u v) = A u
  let C : V → Prop := fun v => (∑ u, D u v) = A v
  have hentry : ∀ u v, F u v ≤
      (if R u then F u v else 0) + (if C v then F u v else 0) := by
    intro u v
    by_cases hpos : 0 < F u v
    · rcases hsat u v hpos with hr | hc
      · have hr' : R u := hr
        simp only [hr', ite_true]
        exact le_add_of_nonneg_right (by split_ifs <;> simp [hF u v])
      · have hc' : C v := hc
        simp only [hc', ite_true]
        exact le_add_of_nonneg_left (by split_ifs <;> simp [hF u v])
    · have hz : F u v = 0 := le_antisymm (le_of_not_gt hpos) (hF u v)
      simp [hz]
  have hrows : (∑ u, ∑ v, if R u then F u v else 0) ≤
      (demandSize D : ℝ) := by
    have hrow' : ∀ u, (∑ v, if R u then F u v else 0) ≤
        ((∑ v, D u v : ℕ) : ℝ) := by
      intro u
      by_cases hr : R u
      · simp only [hr, ite_true]
        exact (hrow u).trans_eq (congrArg (fun n : ℕ => (n : ℝ)) hr.symm)
      · simp only [hr, ite_false, sum_const_zero]
        exact Nat.cast_nonneg _
    simpa [demandSize] using sum_le_sum (fun u (_ : u ∈ (univ : Finset V)) => hrow' u)
  have hcols : (∑ u, ∑ v, if C v then F u v else 0) ≤
      (demandSize D : ℝ) := by
    rw [sum_comm]
    have hcol' : ∀ v, (∑ u, if C v then F u v else 0) ≤
        ((∑ u, D u v : ℕ) : ℝ) := by
      intro v
      by_cases hc : C v
      · simp only [hc, ite_true]
        exact (hcol v).trans_eq (congrArg (fun n : ℕ => (n : ℝ)) hc.symm)
      · simp only [hc, ite_false, sum_const_zero]
        exact Nat.cast_nonneg _
    have hsum := sum_le_sum (fun v (_ : v ∈ (univ : Finset V)) => hcol' v)
    have htotal : (∑ v, ∑ u, D u v) = demandSize D := by
      rw [sum_comm]
      rfl
    simpa only [← Nat.cast_sum, htotal] using hsum
  have hcover : (∑ u, ∑ v, F u v) ≤
      (∑ u, ∑ v, if R u then F u v else 0) +
      (∑ u, ∑ v, if C v then F u v else 0) := by
    calc
      _ ≤ ∑ u, ∑ v, ((if R u then F u v else 0) +
          (if C v then F u v else 0)) :=
        sum_le_sum fun u _ => sum_le_sum fun v _ => hentry u v
      _ = _ := by simp only [sum_add_distrib]
  linarith

/-- Support-preserving factor-two integral extraction for a nonnegative real
matrix with integral row and column budgets. The conclusion preserves positivity
support, not the entrywise fractional upper bounds. -/
theorem exists_integral_support_extraction
    (F : V → V → ℝ) (A : NodeWeight V)
    (hF : ∀ u v, 0 ≤ F u v)
    (hrow : ∀ u, (∑ v, F u v) ≤ (A u : ℝ))
    (hcol : ∀ v, (∑ u, F u v) ≤ (A v : ℝ)) :
    ∃ D : Demand V, Respects D A ∧ (∀ u v, 0 < D u v → 0 < F u v) ∧
      (∑ u, ∑ v, F u v) ≤ 2 * (demandSize D : ℝ) := by
  obtain ⟨D, hD, hsupport, hsat⟩ :=
    exists_saturated_supported_demand A (fun u v => 0 < F u v)
  exact ⟨D, hD, hsupport, fractional_mass_le_twice_of_saturated F A D hF hrow hcol hsat⟩

end LengthExpander
