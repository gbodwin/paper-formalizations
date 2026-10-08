import LinearDistancePreservers.FinitePerturbation
import LinearDistancePreservers.WeightedNativeForcing

/-! Realize the small-epsilon argument by actual nonnegative edge weights
on a finite graph. The same scale works for every pair of simple paths,
including all endpoint pairs. This supplies the analytic step needed by the
weighted obstacle product; its lexicographic path comparison remains to be
proved from the outer/inner graph projection. -/
namespace LinearDistancePreservers.WeightedNativeForcing
open SimpleGraph Finset
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {V : Type*} {G : SimpleGraph V}

theorem realCost_add_scale (w₀ w₁ : V → V → ℝ≥0) (δ : ℝ≥0)
    {s t : V} (p : G.Walk s t) :
    realCost (fun u v => w₀ u v + δ * w₁ u v) p =
      realCost w₀ p + (δ : ℝ) * realCost w₁ p := by
  unfold realCost
  rw [darts_sum_eq (fun u v => ((w₀ u v + δ * w₁ u v : ℝ≥0) : ℝ)) p,
    darts_sum_eq (fun u v => (w₀ u v : ℝ)) p,
    darts_sum_eq (fun u v => (w₁ u v : ℝ)) p]
  simp only [NNReal.coe_add, NNReal.coe_mul, sum_add_distrib, mul_sum]

/-- Strict lexicographic comparisons between simple native paths are
preserved by one common positive perturbation of actual edge weights. -/
theorem exists_path_perturbation [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w₀ w₁ : V → V → ℝ≥0) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ δ : ℝ≥0, 0 < δ → δ ≤ ε →
      ∀ s t (p q : G.Path s t),
      (realCost w₀ p.val < realCost w₀ q.val ∨
        (realCost w₀ p.val = realCost w₀ q.val ∧ realCost w₁ p.val < realCost w₁ q.val)) →
      realCost (fun u v => w₀ u v + δ * w₁ u v) p.val <
        realCost (fun u v => w₀ u v + δ * w₁ u v) q.val := by
  classical
  let X := Σ s : V, Σ t : V, G.Path s t
  let f : X → ℝ := fun p => realCost w₀ p.2.2.val
  let g : X → ℝ := fun p => realCost w₁ p.2.2.val
  obtain ⟨ε, hε, hcompare⟩ := exists_uniform_perturbation f g
  refine ⟨⟨ε, hε.le⟩, ?_, ?_⟩
  · exact_mod_cast hε
  · intro δ hδ hδε s t p q hpq
    rw [realCost_add_scale, realCost_add_scale]
    exact hcompare (δ : ℝ) (by exact_mod_cast hδ) (by exact_mod_cast hδε)
      ⟨s,t,p⟩ ⟨s,t,q⟩ hpq

end LinearDistancePreservers.WeightedNativeForcing
