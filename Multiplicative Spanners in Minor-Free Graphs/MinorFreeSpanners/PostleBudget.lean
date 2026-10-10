import MinorFreeSpanners.CoreParameters

/-! A disclosed real-parameter rounding boundary in the cited Postle proof.
The required density-increment regime has d>=k^2 with k>=100, so the valid
3Kd budget below suffices; the unrestricted displayed arithmetic is not used. -/
namespace MinorFreeSpanners

/-- The displayed 3Kd rounding step is valid in the density-increment regime. -/
theorem postle_vertex_budget (K d ε : ℝ) (hK : 1 ≤ K) (hd : 2 ≤ d)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1+K*d+(⌈ε*d⌉₊:ℝ) ≤ 3*K*d := by
  have hceil := Nat.ceil_lt_add_one (mul_nonneg hε0 (by linarith : 0 ≤ d))
  have hKd : d ≤ K*d := by nlinarith
  have hed : ε*d ≤ d := by nlinarith
  linarith

/-- Without d>=2, the same argument has the always valid 4Kd constant. -/
theorem postle_vertex_budget_all_d (K d ε : ℝ) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1+K*d+(⌈ε*d⌉₊:ℝ) ≤ 4*K*d := by
  have hceil := Nat.ceil_lt_add_one (mul_nonneg hε0 (by linarith : 0 ≤ d))
  have hKd : d ≤ K*d := by nlinarith
  have hed : ε*d ≤ d := by nlinarith
  linarith

/-- A rational counterexample to the printed arithmetic step on Postle v3,
page6. This does not refute Proposition3.2 or the spanner paper's main theorem. -/
theorem postle_displayed_rounding_step_counterexample :
    (1:ℝ) ≤ 1 ∧ (1:ℝ) ≤ 11/10 ∧ (0:ℝ) < 99/100 ∧ (99/100:ℝ) < 1 ∧
      ¬ (1+(1:ℝ)*(11/10)+(⌈(99/100:ℝ)*(11/10)⌉₊:ℝ) ≤ 3*(1:ℝ)*(11/10)) := by
  have hceil : ⌈(99/100:ℝ)*(11/10)⌉₊ = 2 := by
    apply (Nat.ceil_eq_iff (by decide : 2 ≠ 0)).mpr
    norm_num
  rw [hceil]
  norm_num

end MinorFreeSpanners
