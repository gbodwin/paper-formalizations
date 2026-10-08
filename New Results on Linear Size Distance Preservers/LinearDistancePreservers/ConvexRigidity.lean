import LinearDistancePreservers.DirectionGraph
import Mathlib.Analysis.Convex.Combination

/-! The paper's geometric condition implies the average-rigidity property
used by the native graph proof. The condition is expressed using mathlib's
convex hull of all other direction vectors, with no graph assumptions. -/
namespace LinearDistancePreservers.DirectionGraph
open Finset
attribute [local instance] Classical.propDecidable
variable {D J : Type*}

def realVector (v : J → D → ℕ) (a : J) : D → ℝ := fun d => (v a d : ℝ)

/-- Each vector is outside the convex hull of the other vectors. The
paper's prohibition of combinations with total coefficient at most one
implies this (ordinary convex combinations have total coefficient one). -/
def ConvexPosition (v : J → D → ℕ) : Prop :=
  ∀ a, realVector v a ∉ convexHull ℝ (Set.range (realVector v) \ {realVector v a})

/-- Removing repetitions of the target from a nonconstant average
expresses it as a convex combination of other vectors, a contradiction. -/
theorem convexPosition_rigid (v : J → D → ℕ) (hc : ConvexPosition v) : AverageRigid v := by
  intro m a f hsum i
  by_contra hne
  let B : Finset (Fin m) := univ.filter fun j => v (f j) ≠ v a
  have hi : i ∈ B := mem_filter.mpr ⟨mem_univ _,hne⟩
  have hB : 0 < B.card := card_pos.mpr ⟨i,hi⟩
  have hBr : (B.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hsumB (d : D) : ∑ j ∈ B, realVector v (f j) d = (B.card : ℝ)*realVector v a d := by
    have hall : ∑ j : Fin m, ((v (f j) d : ℝ)-(v a d : ℝ)) = 0 := by
      rw [sum_sub_distrib]
      have hh : ∑ j : Fin m, (v (f j) d : ℝ) = (m : ℝ)*(v a d : ℝ) := by exact_mod_cast hsum d
      simp [hh]
    have hremove : ∑ j ∈ B, ((v (f j) d : ℝ)-(v a d : ℝ)) =
        ∑ j : Fin m, ((v (f j) d : ℝ)-(v a d : ℝ)) := by
      apply sum_subset (subset_univ B)
      intro j _ hj
      have hj' : v (f j) = v a := by simpa [B] using hj
      rw [hj',sub_self]
    rw [← hremove,sum_sub_distrib] at hall
    simp only [sum_const,nsmul_eq_mul] at hall
    change ∑ j ∈ B, (v (f j) d : ℝ) = (B.card : ℝ)*(v a d : ℝ)
    linarith
  have hcoeff : ∑ j ∈ B, (B.card : ℝ)⁻¹ = 1 := by
    simp [hBr]
  have hmem : (∑ j ∈ B, (B.card : ℝ)⁻¹ • realVector v (f j)) ∈
      convexHull ℝ (Set.range (realVector v) \ {realVector v a}) := by
    apply (convex_convexHull ℝ _).sum_mem (fun _ _ => inv_nonneg.mpr (by positivity)) hcoeff
    intro j hj
    apply subset_convexHull
    refine ⟨⟨f j,rfl⟩,?_⟩
    intro h
    have hh : realVector v (f j) = realVector v a := Set.mem_singleton_iff.mp h
    apply (mem_filter.mp hj).2
    funext d
    have hd := congrFun hh d
    change (v (f j) d : ℝ) = (v a d : ℝ) at hd
    exact_mod_cast hd
  have heq : (∑ j ∈ B, (B.card : ℝ)⁻¹ • realVector v (f j)) = realVector v a := by
    funext d
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,← mul_sum,hsumB]
    rw [← mul_assoc,inv_mul_cancel₀ hBr,one_mul]
  exact hc a (heq ▸ hmem)

/-- Theorem 6's native shortest-path conclusion directly from the
paper's convex-position input, without an abstract path uniqueness input. -/
theorem canonical_unique_of_convexPosition {n k r : ℕ}
    (v : J → D → ℕ) (hv : ∀ a d, v a d < r) (hn : (k+1)*r ≤ n)
    (hc : ConvexPosition v) (s : D → ZMod n) (a : J)
    (q : (graph v n k).Walk (point v s a 0) (point v s a (Fin.last k)))
    (hq : q.length ≤ k) : q = canonicalWalk v s a :=
  canonical_unique v hv hn (convexPosition_rigid v hc) s a q hq

end LinearDistancePreservers.DirectionGraph
