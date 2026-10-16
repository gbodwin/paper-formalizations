import LightEFTSpanners.NativeGreedySoundness

/-! A complete list of actual original IDs, ordered for the tail-first fold.
No seed disjointness is needed: already selected identities are skipped. -/
namespace LightEFTSpanners.NativeWeighted
open Finset
open scoped NNReal
variable {V E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

noncomputable def nativeInput (G : Graph V E) (w : E → ℝ≥0) : List E :=
  (inputEdges G).toList.mergeSort (fun e d => decide (w d ≤ w e))

theorem nativeInput_perm (G : Graph V E) (w : E → ℝ≥0) :
    (nativeInput G w).Perm (inputEdges G).toList := List.mergeSort_perm _ _

@[simp] theorem mem_nativeInput (G : Graph V E) (w : E → ℝ≥0) (e : E) :
    e ∈ nativeInput G w ↔ e ∈ inputEdges G := by
  rw [(nativeInput_perm G w).mem_iff,mem_toList]

theorem nativeInput_nodup (G : Graph V E) (w : E → ℝ≥0) :
    (nativeInput G w).Nodup := (nativeInput_perm G w).nodup_iff.mpr (nodup_toList _)

theorem nativeInput_sorted (G : Graph V E) (w : E → ℝ≥0) :
    (nativeInput G w).Pairwise (fun e d => w d ≤ w e) := by
  have h := List.pairwise_mergeSort
    (le := fun e d : E => decide (w d ≤ w e))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; exact hbc.trans hab)
    (by intro a b; simp only [Bool.or_eq_true,decide_eq_true_eq]; exact le_total _ _)
    (inputEdges G).toList
  simpa only [nativeInput,decide_eq_true_eq] using h

@[simp] theorem nativeInput_toFinset (G : Graph V E) (w : E → ℝ≥0) :
    (nativeInput G w).toFinset = inputEdges G := by
  classical
  ext e
  simp

noncomputable def nativeOutput (G : Graph V E) (w : E → ℝ≥0) (t : ℝ≥0)
    (f : ℕ) (H : Finset E) : Finset E := by
  classical
  exact nativeGreedy G w t f H (nativeInput G w)

/-- A canonical EFT spanner for every f, including zero, without positivity
of individual edge weights, a seed optimum, or a sampling budget. -/
theorem nativeOutput_sound (G : Graph V E) (w : E → ℝ≥0) (t : ℝ≥0)
    (ht : 1 ≤ t) (f : ℕ) (H : Finset E) (hH : H ⊆ inputEdges G) :
    IsEFTSpanner G w (inputEdges G) (nativeOutput G w t f H) f t := by
  classical
  have h := nativeGreedy_sound G w t ht f H (nativeInput G w)
  simpa only [nativeInput_toFinset,union_eq_right.mpr hH] using h

theorem nativeOutput_seed_subset (G : Graph V E) (w : E → ℝ≥0) (t : ℝ≥0)
    (f : ℕ) (H : Finset E) : H ⊆ nativeOutput G w t f H := by
  classical
  exact nativeGreedy_seed_subset G w t f H (nativeInput G w)

end LightEFTSpanners.NativeWeighted
