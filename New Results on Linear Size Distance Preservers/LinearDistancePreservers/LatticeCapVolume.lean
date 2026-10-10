import LinearDistancePreservers.LatticeCaps
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LinearDistancePreservers.LatticeCaps
open MeasureTheory Metric

/-- All caps of height at most δ, including their spherical boundary.
This union may be over arbitrarily many directions. -/
def shallowCaps (d : ℕ) (R δ : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∃ (u : Fin d → ℝ) (h : ℝ), normSq u = 1 ∧ 0 ≤ h ∧ h ≤ δ ∧
    (fun i => x i) ∈ cap u R h}

theorem shallowCaps_subset_annulus {d : ℕ} {R δ : ℝ} (hδ : δ ≤ R) :
    shallowCaps d R δ ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin d)) R \ closedBall 0 (R-δ) := by
  rintro x ⟨u,h,hu,hh,hhδ,hx⟩
  have hs := cap_subset_shell u R h hu (hhδ.trans hδ) hx
  have he : normSq (fun i => x i) = ‖x‖^2 :=
    (EuclideanSpace.real_norm_sq_eq x).symm
  change (R-h)^2 < normSq (fun i => x i) ∧ normSq (fun i => x i) ≤ R^2 at hs
  rw [he] at hs
  have hnorm := norm_nonneg x
  constructor
  · simp only [mem_closedBall, dist_zero_right]
    nlinarith
  · simp only [mem_closedBall, dist_zero_right, not_le]
    nlinarith

/-- The shallow-cap contribution is bounded by the actual Euclidean
annulus volume, with the explicit dimension factor. This establishes the
measure-theoretic shallow-cap step of the sharp-count argument. -/
theorem shallowCaps_volume_bound (n : ℕ) (R δ : ℝ) (h0 : 0 ≤ δ) (hδ : δ ≤ R) :
    volume.real (shallowCaps (n+1) R δ) ≤
      (n+1 : ℕ)*R^n*δ*volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1) := by
  have hR : 0 ≤ R := h0.trans hδ
  have hinner : 0 ≤ R-δ := by linarith
  have hsub := shallowCaps_subset_annulus (d := n+1) hδ
  have houter : volume (closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) R) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  have hfinite : volume (closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) R \ closedBall 0 (R-δ)) ≠ ⊤ := by
    exact measure_ne_top_of_subset Set.sdiff_subset houter
  have hmono := measureReal_mono hsub hfinite
  have hballs : closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) (R-δ) ⊆ closedBall 0 R :=
    closedBall_subset_closedBall (by linarith)
  rw [measureReal_sdiff hballs measurableSet_closedBall houter] at hmono
  rw [Measure.addHaar_real_closedBall' volume _ hR,
    Measure.addHaar_real_closedBall' volume _ hinner] at hmono
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hmono
  have hp := mul_le_mul_of_nonneg_right (annulus_power_bound R δ h0 hδ n)
    (measureReal_nonneg (μ := volume) (s := closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1))
  nlinarith

/-- At the critical cap height, the shallow-cap contribution has the
sharp exponent d(d-1)/(d+1), here with d=n+1. This proves the shallow-cap
part only; deep caps still require arithmetic flatness and summation. -/
theorem shallowCaps_critical_volume (n : ℕ) (R : ℝ) (hR : 1 ≤ R) :
    volume.real (shallowCaps (n+1) R (R^(-(n : ℝ)/(n+2)))) ≤
      (n+1 : ℕ)*R^(((n+1 : ℕ) : ℝ)*n/(n+2))*
        volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1) := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hδ0 : 0 ≤ R^(-(n : ℝ)/(n+2)) := Real.rpow_nonneg hRpos.le _
  have hδ : R^(-(n : ℝ)/(n+2)) ≤ R :=
    (Real.rpow_le_one_of_one_le_of_nonpos hR (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by positivity))).trans hR
  have hh := shallowCaps_volume_bound n R _ hδ0 hδ
  have he : R^n*R^(-(n : ℝ)/(n+2)) = R^(((n+1 : ℕ) : ℝ)*n/(n+2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hRpos]
    congr 1
    push_cast
    field_simp
    ring
  calc
    _ ≤ _ := hh
    _ = _ := by rw [mul_assoc ((n+1 : ℕ) : ℝ) (R^n) _,he]

end LinearDistancePreservers.LatticeCaps
