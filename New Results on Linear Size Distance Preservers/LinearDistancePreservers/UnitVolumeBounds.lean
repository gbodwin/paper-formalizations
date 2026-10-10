import LinearDistancePreservers.LatticeMinima
import LinearDistancePreservers.LatticeMissedVolume

namespace LinearDistancePreservers.LatticeCaps
open Set Metric MeasureTheory Finset

noncomputable def coordinateCube (d : ℕ) (r : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, |x i| ≤ r}

theorem coordinateCube_volume (d : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (coordinateCube d r) = (2*r)^d := by
  let T : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-r) r)
  have hT : MeasurableSet T := MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Icc)
  have hf := PiLp.volume_preserving_ofLp (Fin d)
  have he : coordinateCube d r = (fun x : EuclideanSpace ℝ (Fin d) => WithLp.ofLp x) ⁻¹' T := by
    ext x; simp [coordinateCube,T,abs_le,Pi.le_def,forall_and]
  rw [he,hf.measureReal_preimage hT.nullMeasurableSet]
  change (volume T).toReal = _
  rw [volume_pi_pi,ENNReal.toReal_prod]
  have he' : (∏ i : Fin d, (volume (Set.Icc (-r) r)).toReal) = ∏ _i : Fin d, 2*r := by
    apply Finset.prod_congr rfl
    intro i _
    rw [Real.volume_Icc,ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [he']
  simp

theorem coordinateCube_subset_unitBall {d : ℕ} (hd : 0 < d) :
    coordinateCube d (1/(d : ℝ)) ⊆ closedBall 0 1 := by
  intro x hx
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by positivity
  have hsq (i : Fin d) : (x i)^2 ≤ (1/(d : ℝ))^2 := by
    have hh := hx i
    have := abs_nonneg (x i)
    have := sq_abs (x i)
    nlinarith
  have hsum : ∑ i, (x i)^2 ≤ (d : ℝ)*(1/(d : ℝ))^2 := by
    calc
      _ ≤ ∑ _i : Fin d, (1/(d : ℝ))^2 := Finset.sum_le_sum (fun i _ => hsq i)
      _ = _ := by simp
  have hden : (d : ℝ)*(1/(d : ℝ))^2 ≤ 1 := by
    field_simp
    nlinarith
  rw [← EuclideanSpace.real_norm_sq_eq] at hsum
  simp only [mem_closedBall,dist_zero_right]
  nlinarith [norm_nonneg x]

theorem unitBall_subset_coordinateCube (d : ℕ) :
    closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ coordinateCube d 1 := by
  intro x hx i
  have hxnorm : ‖x‖ ≤ 1 := by simpa using hx
  have hsq : (x i)^2 ≤ ‖x‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have := sq_abs (x i)
  have := abs_nonneg (x i)
  nlinarith [norm_nonneg x]

/-- Elementary dimension-explicit bounds, avoiding special-function estimates. -/
theorem unitBall_volume_bounds {d : ℕ} (hd : 0 < d) :
    (2/(d : ℝ))^d ≤ volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ∧
    volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ≤ 2^d := by
  constructor
  · have hh := measureReal_mono (μ := volume) (coordinateCube_subset_unitBall hd) measure_closedBall_lt_top.ne
    rw [coordinateCube_volume d (by positivity)] at hh
    simpa [div_eq_mul_inv] using hh
  · have hf : volume (coordinateCube d 1) ≠ ⊤ := by
      have hcube : coordinateCube d 1 ⊆ closedBall 0 (d : ℝ) := by
        intro x hx
        have hsq : ‖x‖^2 ≤ (d : ℝ) := by
          rw [EuclideanSpace.real_norm_sq_eq]
          calc
            _ ≤ ∑ _i : Fin d, (1:ℝ) := by
              apply Finset.sum_le_sum; intro i _
              have hh := hx i
              have := sq_abs (x i)
              have := abs_nonneg (x i)
              nlinarith
            _ = _ := by simp
        have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
        simp only [mem_closedBall,dist_zero_right]
        nlinarith [norm_nonneg x]
      exact measure_ne_top_of_subset hcube measure_closedBall_lt_top.ne
    have hh := measureReal_mono (unitBall_subset_coordinateCube d) hf
    rw [coordinateCube_volume d (by norm_num)] at hh
    simpa using hh

/-- The neighboring-dimensional volume ratio has an elementary explicit bound. -/
theorem unitBall_volume_ratio (n : ℕ) :
    volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1) /
        volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+2))) 1) ≤
      ((n+2 : ℕ) : ℝ)^(n+2)/2 := by
  let d := n+2
  let V := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+2))) 1)
  let U := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1)
  have hlo := (unitBall_volume_bounds (d := n+2) (by omega)).1
  have hup := (unitBall_volume_bounds (d := n+1) (by omega)).2
  have hd : (0:ℝ) < (n+2 : ℕ) := by positivity
  have hV : 0 < V := lt_of_lt_of_le (by positivity : 0 < (2/((n+2 : ℕ):ℝ))^(n+2)) hlo
  have hmul := mul_le_mul_of_nonneg_right hlo (by positivity : 0 ≤ ((n+2 : ℕ):ℝ)^(n+2))
  have hid : (2/((n+2 : ℕ):ℝ))^(n+2)*((n+2 : ℕ):ℝ)^(n+2) = 2^(n+2) := by
    rw [← mul_pow,div_mul_cancel₀ _ hd.ne']
  rw [hid] at hmul
  have hpow : (2:ℝ)^(n+2)=2^(n+1)*2 := by rw [show n+2=(n+1)+1 by omega,pow_succ]
  apply (div_le_iff₀ hV).mpr
  change U ≤ ((n+2 : ℕ):ℝ)^(n+2)/2*V
  change U ≤ (2:ℝ)^(n+1) at hup
  change (2:ℝ)^(n+2) ≤ V*((n+2 : ℕ):ℝ)^(n+2) at hmul
  rw [hpow] at hmul
  nlinarith

end LinearDistancePreservers.LatticeCaps
