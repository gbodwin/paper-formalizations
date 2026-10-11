import MinorFreeSpanners.GeneralResidualCoverage
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! The actual high-degree vertex count is paid by the complete original
host degree sum. All thresholds refer to the same graph and density scale. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem originalLargeVertices_degree_budget (G : SimpleGraph V) (D : ℝ) :
    D*(originalLargeVertices G D).card ≤ 2*(G.edgeFinset.card:ℝ) := by
  classical
  calc
    _ = ∑ _x ∈ originalLargeVertices G D, D := by simp [mul_comm]
    _ ≤ ∑ x ∈ originalLargeVertices G D, (G.degree x:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      exact (Finset.mem_filter.mp hx).2.le
    _ = ((∑ x ∈ originalLargeVertices G D, G.degree x):ℕ) := by simp
    _ ≤ ((∑ x : V, G.degree x):ℕ) := by
      exact_mod_cast Finset.sum_le_sum_of_subset (Finset.subset_univ (originalLargeVertices G D))
    _ = _ := by rw [G.sum_degrees_eq_twice_card_edges];simp only [Nat.cast_mul,Nat.cast_ofNat]

omit [DecidableEq V] in
theorem originalLargeVertices_scaled_card (G : SimpleGraph V) (k : ℕ) (K d : ℝ)
    (hd : 0 < d) (hK : 4*(k:ℝ)^2 ≤ K)
    (hE : (G.edgeFinset.card:ℝ) ≤ d*(Fintype.card V:ℝ)) :
    2*k^2*(originalLargeVertices G (K*d)).card ≤ Fintype.card V := by
  have hbudget := (originalLargeVertices_degree_budget G (K*d)).trans
    (mul_le_mul_of_nonneg_left hE (by norm_num))
  have hscale := mul_le_mul_of_nonneg_right hK
    (mul_nonneg hd.le (Nat.cast_nonneg (originalLargeVertices G (K*d)).card))
  have hh : (2*d)*(2*(k:ℝ)^2*(originalLargeVertices G (K*d)).card) ≤
      (2*d)*(Fintype.card V:ℝ) := by nlinarith
  have hh' := le_of_mul_le_mul_left hh (show 0 < 2*d by positivity)
  exact_mod_cast hh'

/-- The actual large-or-exceptional target is at most 3N/(2k), expressed
without division. This uses the proved one-heavy-vertex-per-star property. -/
theorem residualTargetVertices_scaled_card (G : SimpleGraph V) (k : ℕ)
    (C : Finset V) (L : V → Finset V) (K d threshold : ℝ)
    (hk : 1 ≤ k) (hd : 0 < d) (hK : 4*(k:ℝ)^2 ≤ K)
    (hE : (G.edgeFinset.card:ℝ) ≤ d*(Fintype.card V:ℝ))
    (hF : IsGeneralStarForest G k C L)
    (hbranch : ∀ b ∈ C, (largeResidualStarVertices G C L (K*d) threshold b).card ≤ 1) :
    2*k*(residualTargetVertices G C L (K*d) threshold).card ≤ 3*Fintype.card V := by
  have hB := originalLargeVertices_scaled_card G k K d hd hK hE
  have hH := exceptionalCoveredVertices_size G k C L (K*d) threshold hF hbranch
  have hB' : 2*k*(originalLargeVertices G (K*d)).card ≤ Fintype.card V := by
    have hkk : k ≤ k^2 := by nlinarith
    have hh := Nat.mul_le_mul_right (2*(originalLargeVertices G (K*d)).card) hkk
    nlinarith
  have hY : (residualTargetVertices G C L (K*d) threshold).card ≤
      (originalLargeVertices G (K*d)).card+(exceptionalCoveredVertices G C L (K*d) threshold).card :=
    Finset.card_union_le _ _
  have hh := Nat.mul_le_mul_left (2*k) hY
  nlinarith

end MinorFreeSpanners
