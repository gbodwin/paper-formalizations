import LinearDistancePreservers.RootRate
import LinearDistancePreservers.UnitVolumeBounds

namespace LinearDistancePreservers.LatticeCaps
open MeasureTheory Metric

/-- Coarse polynomial-in-d powers controlling the explicit flatness constants. -/
theorem flatness_power_bounds {d : ℕ} (hd : 3 ≤ d) :
    let x := (d : ℝ)
    let W := 8*x^(d+1)
    let H := W^2+3*W
    1 ≤ W ∧ W+1 ≤ x^(d+4) ∧ H ≤ x^(2*d+7) ∧
      2*(W+2) ≤ x^(d+5) ∧ H+1 ≤ x^(2*d+8) := by
  let x := (d : ℝ)
  let W := 8*x^(d+1)
  let H := W^2+3*W
  have hx3 : (3:ℝ) ≤ x := by dsimp [x]; exact_mod_cast hd
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by positivity
  have hp : 1 ≤ x^(d+1) := one_le_pow₀ hx1
  have hW3 : 3 ≤ W := by dsimp [W]; linarith
  have hW0 : 0 ≤ W := by positivity
  have hW : W ≤ x^(d+3) := by
    calc
      _ ≤ x^2*x^(d+1) := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hH0 : 1 ≤ H := by dsimp [H]; nlinarith
  have hWplus : W+1 ≤ x^(d+4) := by
    calc
      _ ≤ 2*W := by linarith
      _ ≤ x*W := mul_le_mul_of_nonneg_right (by linarith) hW0
      _ ≤ x*x^(d+3) := mul_le_mul_of_nonneg_left hW hx0
      _ = _ := by rw [← pow_succ']
  have hH : H ≤ x^(2*d+7) := by
    have hH2 : H ≤ 2*W^2 := by
      have hh := mul_le_mul_of_nonneg_right hW3 hW0
      dsimp [H]; nlinarith
    calc
      _ ≤ 2*W^2 := hH2
      _ ≤ x*(x^(d+3))^2 := by gcongr; linarith
      _ = _ := by rw [← pow_mul,← pow_succ']; congr 1; omega
  have hbase : 2*(W+2) ≤ x^(d+5) := by
    calc
      _ ≤ 4*W := by linarith
      _ ≤ x^2*W := mul_le_mul_of_nonneg_right (by nlinarith) hW0
      _ ≤ x^2*x^(d+3) := mul_le_mul_of_nonneg_left hW (sq_nonneg x)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hHp : H+1 ≤ x^(2*d+8) := by
    calc
      _ ≤ 2*H := by linarith
      _ ≤ x*H := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ x*x^(2*d+7) := mul_le_mul_of_nonneg_left hH hx0
      _ = _ := by rw [← pow_succ']
  exact ⟨by linarith,hWplus,hH,hbase,hHp⟩

/-- Coarse explicit dimension growth of the actual deep-cell coefficient. -/
theorem deepCoefficient_ratio_bound (n : ℕ) :
    deepCoefficient n /
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) 1) ≤
      ((n+3 : ℕ) : ℝ)^(12*(n+3)^2) := by
  let d : ℕ := n+3
  let x := (d : ℝ)
  let W := flatnessWidth (n+2)
  let H := depthConstant (n+2)
  let V := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) 1)
  let U := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+2))) 1)
  have hd3 : 3 ≤ d := by dsimp [d]; omega
  have hx3 : (3:ℝ) ≤ x := by dsimp [x]; exact_mod_cast hd3
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by positivity
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_closedBall_pos volume _ (by norm_num : (0:ℝ)<1)).ne'
    measure_closedBall_lt_top.ne
  have hU : 0 ≤ U := measureReal_nonneg
  have hW0 : 0 ≤ W := by dsimp [W,flatnessWidth]; positivity
  have hH0 : 0 ≤ H := by dsimp [H,depthConstant]; positivity
  have hb := flatness_power_bounds hd3
  change 1 ≤ W ∧ W+1 ≤ x^(d+4) ∧ H ≤ x^(2*d+7) ∧
    2*(W+2) ≤ x^(d+5) ∧ H+1 ≤ x^(2*d+8) at hb
  have hbase : (2*(W+2))^((n:ℝ)/2) ≤ x^((d+5)*d) := by
    calc
      _ ≤ (2*(W+2))^(d:ℝ) := Real.rpow_le_rpow_of_exponent_le
        (by linarith [hb.1]) (by dsimp [d]; push_cast; linarith)
      _ = (2*(W+2))^d := Real.rpow_natCast _ _
      _ ≤ (x^(d+5))^d := pow_le_pow_left₀ (by positivity) hb.2.2.2.1 d
      _ = _ := by rw [← pow_mul]
  have hdepth : (H+1)^(((n:ℝ)+2)/2) ≤ x^((2*d+8)*d) := by
    calc
      _ ≤ (H+1)^(d:ℝ) := Real.rpow_le_rpow_of_exponent_le
        (by linarith) (by dsimp [d]; push_cast; linarith)
      _ = (H+1)^d := Real.rpow_natCast _ _
      _ ≤ (x^(2*d+8))^d := pow_le_pow_left₀ (by positivity) hb.2.2.2.2 d
      _ = _ := by rw [← pow_mul]
  have hratio : U/V ≤ x^d := by
    have hh := unitBall_volume_ratio (n+1)
    have hh' : U/V ≤ x^d/2 := by simpa [U,V,x,d,add_assoc] using hh
    exact hh'.trans (by have := pow_nonneg hx0 d; linarith)
  have h16 : (16:ℝ) ≤ x^3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hx3 (n := 3)
    norm_num at hh
    linarith
  have hdim : (n:ℝ)+2 ≤ x := by dsimp [x,d]; push_cast; linarith
  have hthree : (3:ℝ)^(n+2) ≤ x^d := by
    exact (pow_le_pow_left₀ (by norm_num) hx3 (n+2)).trans
      (pow_le_pow_right₀ hx1 (by dsimp [d]; omega))
  have hcoef : (16:ℝ)*x*(n+2)*3^(n+2) ≤ x^(d+5) := by
    calc
      _ ≤ x^3*x*x*x^d := by gcongr
      _ = _ := by ring_nf
  have he : deepCoefficient n / V =
      (16*x*(n+2)*3^(n+2))*(W+1)*H*(2*(W+2))^((n:ℝ)/2)*
        (H+1)^(((n:ℝ)+2)/2)*(U/V) := by
    dsimp [deepCoefficient,cellCoefficient,W,H,U,x,d]
    push_cast
    ring
  rw [he]
  have hWp := hb.2.1
  have hHp := hb.2.2.1
  change _ ≤ x^(12*d^2)
  calc
    _ ≤ x^(d+5)*x^(d+4)*x^(2*d+7)*x^((d+5)*d)*x^((2*d+8)*d)*x^d := by
      gcongr <;> assumption
    _ = x^(3*d^2+18*d+16) := by simp only [← pow_add]; congr 1; ring
    _ ≤ _ := pow_le_pow_right₀ hx1 (by
      have hh := Nat.mul_le_mul_left d hd3
      nlinarith)

/-- An elementary inverse-volume bound. -/
theorem unitBall_volume_reciprocal {d : ℕ} (hd : 0 < d) :
    1 / volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ≤ (d:ℝ)^d := by
  let V := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_closedBall_pos volume _ (by norm_num : (0:ℝ)<1)).ne'
    measure_closedBall_lt_top.ne
  have hh := mul_le_mul_of_nonneg_right (unitBall_volume_bounds hd).1
    (by positivity : 0 ≤ (d:ℝ)^d)
  have he : (2/(d:ℝ))^d*(d:ℝ)^d = 2^d := by
    rw [← mul_pow,div_mul_cancel₀ _ hd0.ne']
  rw [he] at hh
  apply (div_le_iff₀ hV).mpr
  change _ ≤ (d:ℝ)^d*V
  have hp : (1:ℝ) ≤ 2^d := one_le_pow₀ (by norm_num)
  change (2:ℝ)^d ≤ V*(d:ℝ)^d at hh
  nlinarith

/-- The actual missed-volume coefficient has an explicit coarse ratio bound. -/
theorem missedCoefficient_ratio_bound (n : ℕ) :
    missedCoefficient n /
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) 1) ≤
      ((n+3 : ℕ) : ℝ)^(12*(n+3)^2+1) := by
  let d : ℕ := n+3
  let x := (d:ℝ)
  let V := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) 1)
  have hd3 : 3 ≤ d := by dsimp [d]; omega
  have hx3 : (3:ℝ) ≤ x := by dsimp [x]; exact_mod_cast hd3
  have hx1 : 1 ≤ x := by linarith
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_closedBall_pos volume _ (by norm_num : (0:ℝ)<1)).ne'
    measure_closedBall_lt_top.ne
  have hdeep := deepCoefficient_ratio_bound n
  have hrecip := unitBall_volume_reciprocal (d := n+3) (by omega)
  have hdexp : d ≤ 12*d^2 := by nlinarith
  have he1 : 1 ≤ 12*d^2 := by nlinarith
  have hxpow : x ≤ x^(12*d^2) := by
    simpa only [pow_one] using pow_le_pow_right₀ hx1 he1
  have hdpow : x^d ≤ x^(12*d^2) := pow_le_pow_right₀ hx1 hdexp
  have he : missedCoefficient n / V = x+deepCoefficient n/V+1/V := by
    change (x*V+deepCoefficient n+1)/V = x+deepCoefficient n/V+1/V
    field_simp [hV.ne'] <;> ring
  rw [he]
  change _ ≤ x^(12*d^2+1)
  rw [pow_succ]
  change deepCoefficient n/V ≤ x^(12*d^2) at hdeep
  change 1/V ≤ x^d at hrecip
  have hh : 3*x^(12*d^2) ≤ x^(12*d^2)*x := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hx3 (by positivity : 0 ≤ x^(12*d^2))
  linarith

/-- The closed sharp-lattice radius factor has a coarse, fully explicit
bound in the dimension. This is a bound for the actual constructed radius. -/
theorem explicitRadius_bound (n : ℕ) :
    LatticeHull.explicitRadius n ≤ (n+3)^(20*(n+3)^2) := by
  let d : ℕ := n+3
  let x := (d:ℝ)
  let H := depthConstant (n+2)
  let A := missedCoefficient n
  let V := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) 1)
  let R₀ := missedThreshold n
  let J : ℕ := 2^(n+5)
  let Z := max (4*(J:ℝ)^2*A/V) (R₀:ℝ)
  have hd3 : 3 ≤ d := by dsimp [d]; omega
  have hx3 : (3:ℝ) ≤ x := by dsimp [x]; exact_mod_cast hd3
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by positivity
  have hdd := Nat.mul_le_mul_left d hd3
  have hA : 0 < A := (concrete_missed_volume_bound n).1
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_closedBall_pos volume _ (by norm_num : (0:ℝ)<1)).ne'
    measure_closedBall_lt_top.ne
  have hH : 0 ≤ H := by dsimp [H,depthConstant,flatnessWidth]; positivity
  have ha : A/V ≤ x^(12*d^2+1) := missedCoefficient_ratio_bound n
  have hJ : (J:ℝ) ≤ x^(d+2) := by
    dsimp [J,x,d]
    push_cast
    apply pow_le_pow_left₀ (by norm_num) (by exact_mod_cast (show 2 ≤ n+3 by omega))
  have hscale : 4*(J:ℝ)^2 ≤ x^(2*d+6) := by
    calc
      _ ≤ x^2*(x^(d+2))^2 := by gcongr; nlinarith
      _ = _ := by rw [← pow_mul,← pow_add]; congr 1; omega
  have hterm : 4*(J:ℝ)^2*A/V ≤ x^(14*d^2) := by
    calc
      _ = (4*(J:ℝ)^2)*(A/V) := by ring
      _ ≤ x^(2*d+6)*x^(12*d^2+1) := mul_le_mul hscale ha
        (div_nonneg hA.le hV.le) (by positivity)
      _ = x^(12*d^2+2*d+7) := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := pow_le_pow_right₀ hx1 (by nlinarith)
  have hb := (flatness_power_bounds hd3).2.2.2.2
  change H+1 ≤ x^(2*d+8) at hb
  have hR₀ : (R₀:ℝ) ≤ x^(14*d^2) := by
    have hc := Nat.ceil_lt_add_one (by linarith : 0 ≤ H+1)
    have hc' : (R₀:ℝ) < H+3 := by
      dsimp [R₀,missedThreshold]
      push_cast
      change (⌈H+1⌉₊:ℝ)+1 < H+3
      linarith
    have hp : 1 ≤ x^(2*d+8) := one_le_pow₀ hx1
    have hm := mul_le_mul_of_nonneg_right hx3 (by positivity : 0 ≤ x^(2*d+8))
    calc
      _ ≤ x^(2*d+8)+2 := by linarith
      _ ≤ x*x^(2*d+8) := by nlinarith
      _ = x^(2*d+9) := by rw [← pow_succ']
      _ ≤ _ := pow_le_pow_right₀ hx1 (by nlinarith)
  have hZ0 : 0 ≤ Z := (Nat.cast_nonneg R₀).trans (le_max_right _ _)
  have hZ : Z ≤ x^(14*d^2) := max_le hterm hR₀
  have hc := Nat.ceil_lt_add_one hZ0
  have hp : x ≤ x^(14*d^2) := by
    simpa only [pow_one] using pow_le_pow_right₀ hx1 (show 1 ≤ 14*d^2 by nlinarith)
  have hm := mul_le_mul_of_nonneg_right hx3 (by positivity : 0 ≤ x^(14*d^2))
  have hfinal : ((LatticeHull.explicitRadius n : ℕ):ℝ) ≤ x^(20*d^2) := by
    change ((⌈Z⌉₊+2 : ℕ):ℝ) ≤ x^(20*d^2)
    push_cast
    calc
      _ ≤ x^(14*d^2)+3 := by linarith
      _ ≤ x*x^(14*d^2) := by nlinarith
      _ = x^(14*d^2+1) := by rw [← pow_succ']
      _ ≤ _ := pow_le_pow_right₀ hx1 (by nlinarith)
  dsimp [x,d] at hfinal
  exact_mod_cast hfinal

end LinearDistancePreservers.LatticeCaps
