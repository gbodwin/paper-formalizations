import LinearDistancePreservers.SpherePower

namespace LinearDistancePreservers.SphereScales

def sphereFactor (d : ℕ) : ℕ := 96*(2^(3*d+1)*d)

/-- Both terminal substitution and the small-terminal path baseline fit
one coefficient with only exponential dependence on the dimension. -/
theorem terminal_coefficients {d : ℕ} (hd : 3 ≤ d)
    (hc : 2^((3*d-1)*(d^2-2)+(2*d-2))*d^(d*(d-2)) ≤
      (2^(3*d+1)*d)^(d^2-2)) :
    4^(d*(d-2))*12^((d+1)*(d-2))*
      (2^((3*d-1)*(d^2-2)+(2*d-2))*d^(d*(d-2))) ≤ sphereFactor d^(d^2-2) ∧
    5^(d*(d-2)+(d+1)*(d-2))*2^(d^2-2) ≤ sphereFactor d^(d^2-2) := by
  let D := d^2-2
  let U := 2^(3*d+1)*d
  have hDsub := Nat.sub_add_cancel (show 2≤d^2 by nlinarith)
  have hdsub := Nat.sub_add_cancel (show 2≤d by omega)
  have ha : d*(d-2) ≤ D := by dsimp [D]; nlinarith only [hDsub,hdsub,hd]
  have he : (d+1)*(d-2) ≤ D := by dsimp [D]; nlinarith only [hDsub,hdsub,hd]
  have hU : 1≤U := by dsimp [U]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  constructor
  · calc
      _ ≤ 4^D*12^D*U^D := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) ha) (Nat.pow_le_pow_right (by omega) he)) hc
      _ = (48*U)^D := by rw [← mul_pow,← mul_pow]; norm_num
      _ ≤ _ := Nat.pow_le_pow_left (by dsimp [sphereFactor,U]; omega) _
  · calc
      _ ≤ 5^(2*D)*2^D := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
      _ = 50^D := by rw [pow_mul,← mul_pow]; norm_num
      _ ≤ _ := Nat.pow_le_pow_left (by change 50≤96*U; omega) _

/-- A simple logarithm-free envelope for the literal sphere coefficient. -/
theorem sphereFactor_le_exp {d : ℕ} (hd : 3 ≤ d) :
    (sphereFactor d : ℝ) ≤ Real.exp (7*(d : ℝ)) := by
  have htwo : (2 : ℝ)≤Real.exp 1 := by have h := Real.add_one_le_exp (1 : ℝ); norm_num at h; exact h
  have h192 : (192 : ℝ)≤Real.exp 8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤2) htwo 8
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith
  have hdexp : (d : ℝ)≤Real.exp (d : ℝ) := by have h := Real.add_one_le_exp (d : ℝ); linarith
  have hpow : (2 : ℝ)^(3*d)≤Real.exp (3*(d : ℝ)) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤2) htwo (3*d)
    rw [← Real.exp_nat_mul] at h
    simpa using h
  have hdr : (3 : ℝ)≤d := by exact_mod_cast hd
  calc
    _ = 192*(d : ℝ)*2^(3*d) := by unfold sphereFactor; push_cast; rw [pow_succ]; ring
    _ ≤ Real.exp 8*Real.exp (d : ℝ)*Real.exp (3*(d : ℝ)) := by gcongr
    _ = Real.exp (8+4*(d : ℝ)) := by rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end LinearDistancePreservers.SphereScales

