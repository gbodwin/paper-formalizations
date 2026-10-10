import LinearDistancePreservers.CoefficientBounds

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

namespace LinearDistancePreservers.LatticeCaps
open MeasureTheory Metric Set Finset

/-- Scaling the shallow/deep height also scales the integer-normal cutoff;
the explicit scale hypothesis absorbs the ceiling's additive one. -/
theorem scaled_depthRadius_le (n : ℕ) {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hscale : S ≤ R^(((n : ℝ)+2)/(n+4))) :
    (depthRadius (n+2) (S*criticalHeight n R) : ℝ) ≤
      (depthConstant (n+2)+1)*S⁻¹*R^(((n : ℝ)+2)/(n+4)) := by
  let a := ((n : ℝ)+2)/(n+4)
  let C := depthConstant (n+2)
  have hC : 0 ≤ C := by dsimp [C,depthConstant,flatnessWidth]; positivity
  have hp : 0 < R^a := Real.rpow_pos_of_pos hR _
  have he : C/(S*R^(-a)) = C*S⁻¹*R^a := by
    rw [Real.rpow_neg hR.le]
    field_simp
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ C/(S*R^(-a)))
  rw [he] at hceil
  have hs : 1 ≤ S⁻¹*R^a := by
    rw [mul_comm,← div_eq_mul_inv]
    exact (le_div_iff₀ hS).mpr (by simpa [a] using hscale)
  change (⌈C/(S*R^(-a))⌉₊ : ℝ) ≤ (C+1)*S⁻¹*R^a
  rw [he]
  nlinarith only [hceil,hs]


theorem deepCells_scaled_volume (n : ℕ) {R S : ℝ} (hR : 1 ≤ R) (hS : 0 < S)
    (hCR : depthConstant (n+2) ≤ R)
    (hscale : S ≤ R^(((n : ℝ)+2)/(n+4))) :
    volume.real (deepCells (n+2) R (S*criticalHeight n R)) ≤
      (deepCoefficient n*S^(-(((n : ℝ)+2)/2))) *
        R^(((n : ℝ)+3)*((n : ℝ)+2)/(n+4)) := by
  let a := ((n : ℝ)+2)/(n+4)
  let p := ((n : ℝ)+2)/2
  let C := depthConstant (n+2)
  let D := cellCoefficient n (flatnessWidth (n+2)) C
  let F : ℝ := (4*(n+3)*3^(n+2) : ℕ)
  let M := depthRadius (n+2) (S*criticalHeight n R)
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hC : 0 ≤ C := by dsimp [C,depthConstant,flatnessWidth]; positivity
  have hD : 0 ≤ D := by dsimp [D,cellCoefficient,flatnessWidth]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hM : (M : ℝ) ≤ (C+1)*S⁻¹*R^a := scaled_depthRadius_le n hR0 hS hscale
  have hMp : (M : ℝ)^p ≤ ((C+1)*S⁻¹*R^a)^p :=
    Real.rpow_le_rpow (by positivity) hM hp
  have he : R^p*(R^a)^p = R^(((n : ℝ)+3)*((n : ℝ)+2)/(n+4)) := by
    rw [← Real.rpow_mul hR0.le,← Real.rpow_add hR0]
    congr 1
    dsimp [p,a]
    field_simp
    ring
  have hb := deepCells_volume_bound n R (S*criticalHeight n R) hR0 hCR
  change volume.real (deepCells (n+2) R (S*criticalHeight n R)) ≤ D*R^p*F*(M : ℝ)^p at hb
  calc
    _ ≤ D*R^p*F*(M : ℝ)^p := hb
    _ ≤ D*R^p*F*(((C+1)*S⁻¹*R^a)^p) :=
      mul_le_mul_of_nonneg_left hMp (by positivity)
    _ = (D*F*(C+1)^p)*(S^(-p))*(R^p*(R^a)^p) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hR0.le _),
        Real.mul_rpow (by positivity) (by positivity),Real.inv_rpow hS.le,
        ← Real.rpow_neg hS.le]
      ring
    _ = _ := by rw [he]; rfl


/-- A genuine rescaled missed-region estimate. This is an actual volume
bound, not a caller-supplied cap-volume certificate. -/
theorem missed_scaled_volume (n R : ℕ) {S : ℝ} (hR : (1 : ℝ) ≤ R) (hS : 0 < S)
    (hCR : depthConstant (n+2) ≤ R)
    (hscale : S ≤ (R : ℝ)^(((n : ℝ)+2)/(n+4))) :
    volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) R \ LatticeBody.body (n+3) R) ≤
      ((n+3 : ℕ)*S*volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) 1)+
        deepCoefficient n*S^(-(((n : ℝ)+2)/2))) *
        (R : ℝ)^(((n : ℝ)+3)*((n : ℝ)+2)/(n+4)) := by
  let δ := S*criticalHeight n R
  let a := ((n : ℝ)+3)*((n : ℝ)+2)/(n+4)
  let V := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) 1)
  have hR0 : (0 : ℝ) < R := zero_lt_one.trans_le hR
  have hδ : 0 < δ := by dsimp [δ,criticalHeight]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ,criticalHeight]
    rw [Real.rpow_neg hR0.le,← div_eq_mul_inv]
    exact (div_le_one (Real.rpow_pos_of_pos hR0 _)).mpr hscale
  have hδR : δ ≤ (R : ℝ) := hδ1.trans hR
  have hcover := missed_subset_shallow_union_deep (n+2) R δ hδ
  have hfinite : volume (shallowCaps (n+3) R δ ∪ deepCells (n+2) R δ) ≠ ⊤ :=
    measure_ne_top_of_subset (Set.union_subset
      ((shallowCaps_subset_annulus hδR).trans Set.sdiff_subset)
      (deepCells_subset_closedBall (n+2) R δ)) measure_closedBall_lt_top.ne
  have hm := measureReal_mono hcover hfinite
  have hs := shallowCaps_volume_bound (n+2) R δ hδ.le hδR
  have he : (R : ℝ)^(n+2)*δ = S*(R : ℝ)^a := by
    dsimp [δ,criticalHeight]
    rw [mul_left_comm,← Real.rpow_natCast R (n+2),← Real.rpow_add hR0]
    congr 2
    dsimp [a]
    push_cast
    field_simp
    ring
  have hs' : volume.real (shallowCaps (n+3) R δ) ≤ (n+3 : ℕ)*S*V*(R : ℝ)^a := by
    have hs0 : volume.real (shallowCaps (n+3) R δ) ≤
        (n+3 : ℕ)*(R : ℝ)^(n+2)*δ*V := by
      simpa [show n+2+1=n+3 by omega,V] using hs
    calc
      _ ≤ (n+3 : ℕ)*(R : ℝ)^(n+2)*δ*V := hs0
      _ = (n+3 : ℕ)*((R : ℝ)^(n+2)*δ)*V := by ring
      _ = _ := by rw [he]; ring
  have hd := deepCells_scaled_volume n hR hS hCR hscale
  have hu := measureReal_union_le (μ := volume) (shallowCaps (n+3) R δ) (deepCells (n+2) R δ)
  change volume.real (deepCells (n+2) R δ) ≤ (deepCoefficient n*S^(-(((n : ℝ)+2)/2)))*(R : ℝ)^a at hd
  change _ ≤ ((n+3 : ℕ)*S*V+deepCoefficient n*S^(-(((n : ℝ)+2)/2)))*(R : ℝ)^a
  nlinarith only [hm,hu,hs',hd]


end LinearDistancePreservers.LatticeCaps


namespace LinearDistancePreservers.LatticeCaps
open MeasureTheory Metric Set

/-- An intentionally coarse balancing multiplier, with logarithm O(d log d). -/
def balanceScale (n : ℕ) : ℕ := (n+3)^(40*(n+3))

noncomputable def balancedCoefficient (n : ℕ) : ℝ :=
  ((n+3 : ℕ)*(balanceScale n : ℝ)+1)*
    volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) 1)

def balancedThreshold (n : ℕ) : ℕ := (balanceScale n)^2

theorem balance_deep_coefficient (n : ℕ) :
    deepCoefficient n*(balanceScale n : ℝ)^(-(((n : ℝ)+2)/2)) ≤
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) 1) := by
  let d : ℕ := n+3
  let x : ℝ := d
  let Q : ℝ := balanceScale n
  let p : ℝ := ((n : ℝ)+2)/2
  let V := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) 1)
  have hd : 3 ≤ d := by dsimp [d]; omega
  have hx : 1 ≤ x := by dsimp [x,d]; exact_mod_cast (show 1 ≤ n+3 by omega)
  have hQ : 0 < Q := by dsimp [Q,balanceScale]; positivity
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_closedBall_pos volume _ (by norm_num : (0 : ℝ)<1)).ne'
    measure_closedBall_lt_top.ne
  have hpower : Q^p = x^(20*d*(d-1)) := by
    have he : ((40*d : ℕ) : ℝ)*p = ((20*d*(d-1) : ℕ) : ℝ) := by
      dsimp [p,d]
      norm_num [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (show 1 ≤ n+3 by omega)]
      ring
    dsimp [Q,balanceScale]
    rw [Nat.cast_pow]
    change (x^(40*d))^p = _
    rw [← Real.rpow_natCast x (40*d),← Real.rpow_mul (by positivity : 0 ≤ x),he,
      Real.rpow_natCast]
  have hexp : 12*d^2 ≤ 20*d*(d-1) := by
    have he : d-1+1=d := Nat.sub_add_cancel (by omega)
    nlinarith
  have hb : deepCoefficient n/V ≤ Q^p := by
    calc
      _ ≤ x^(12*d^2) := deepCoefficient_ratio_bound n
      _ ≤ x^(20*d*(d-1)) := pow_le_pow_right₀ hx hexp
      _ = _ := hpower.symm
  have hD : deepCoefficient n ≤ V*Q^p := by
    have hh := (div_le_iff₀ hV).mp hb
    nlinarith only [hh]
  change deepCoefficient n*Q^(-p) ≤ V
  rw [Real.rpow_neg hQ.le,← div_eq_mul_inv]
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hQ _)).mpr hD


/-- A balanced sharp missed-volume bound, with an explicit integer threshold. -/
theorem balanced_missed_volume_bound (n : ℕ) :
    0 < balancedCoefficient n ∧ ∀ R : ℕ, balancedThreshold n ≤ R →
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) R \ LatticeBody.body (n+3) R) ≤
        balancedCoefficient n*(R : ℝ)^(((n : ℝ)+3)*((n : ℝ)+2)/(n+4)) := by
  let d : ℕ := n+3
  let x : ℝ := d
  let Q : ℝ := balanceScale n
  let V := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) 1)
  let a : ℝ := ((n : ℝ)+2)/(n+4)
  have hd : 3 ≤ d := by dsimp [d]; omega
  have hx : 1 ≤ x := by dsimp [x,d]; exact_mod_cast (show 1 ≤ n+3 by omega)
  have hQ : 0 < Q := by dsimp [Q,balanceScale]; positivity
  have hQ1 : 1 ≤ Q := by
    dsimp [Q,balanceScale]
    exact_mod_cast (one_le_pow₀ (show 1 ≤ n+3 by omega) : 1 ≤ (n+3)^(40*(n+3)))
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_closedBall_pos volume _ (by norm_num : (0 : ℝ)<1)).ne'
    measure_closedBall_lt_top.ne
  have hA : 0 < balancedCoefficient n := by
    change 0 < ((n+3 : ℕ)*Q+1)*V
    exact mul_pos (add_pos_of_nonneg_of_pos (mul_nonneg (Nat.cast_nonneg _) hQ.le) zero_lt_one) hV
  refine ⟨hA,?_⟩
  intro R hR
  have hQR : Q^2 ≤ (R : ℝ) := by
    have hh : (((balanceScale n)^2 : ℕ) : ℝ) ≤ (R : ℝ) := Nat.cast_le.mpr hR
    simpa only [Nat.cast_pow] using hh
  have hR1 : (1 : ℝ) ≤ R := (one_le_pow₀ hQ1 : (1 : ℝ) ≤ Q^2).trans hQR
  have ha : 0 ≤ a := div_nonneg
    (add_nonneg (Nat.cast_nonneg n) (by norm_num))
    (add_nonneg (Nat.cast_nonneg n) (by norm_num))
  have ha2 : 1 ≤ 2*a := by
    dsimp [a]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num) : (0 : ℝ)<(n : ℝ)+4)).mpr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hscale : Q ≤ (R : ℝ)^a := by
    calc
      Q = Q^(1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Q^(2*a) := Real.rpow_le_rpow_of_exponent_le hQ1 ha2
      _ = (Q^2)^a := by rw [← Real.rpow_natCast Q 2,← Real.rpow_mul hQ.le]; norm_num
      _ ≤ _ := Real.rpow_le_rpow (sq_nonneg Q) hQR ha
  have hCR : depthConstant (n+2) ≤ (R : ℝ) := by
    have hh := (flatness_power_bounds hd).2.2.1
    change depthConstant (n+2) ≤ x^(2*d+7) at hh
    apply hh.trans
    calc
      x^(2*d+7) ≤ x^(80*d) := pow_le_pow_right₀ hx (by omega)
      _ = Q^2 := by
        have hQeq : Q=x^(40*d) := by dsimp [Q,balanceScale,x,d]; rw [Nat.cast_pow]
        rw [hQeq,← pow_mul]
        congr 1
        omega
      _ ≤ _ := hQR
  have hm := missed_scaled_volume n R hR1 hQ hCR hscale
  have hb := balance_deep_coefficient n
  apply hm.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg R) _)
  change ((n+3 : ℕ)*Q*V+deepCoefficient n*Q^(-(((n : ℝ)+2)/2))) ≤ ((n+3 : ℕ)*Q+1)*V
  change deepCoefficient n*Q^(-(((n : ℝ)+2)/2)) ≤ V at hb
  nlinarith only [hb]

end LinearDistancePreservers.LatticeCaps

