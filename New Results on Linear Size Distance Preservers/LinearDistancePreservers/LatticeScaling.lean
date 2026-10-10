import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith

namespace LinearDistancePreservers.LatticeScaling

/-- An eventual integer-power count absorbs both its multiplicative constant
and its starting threshold into one radius factor. No monotonicity of F is
assumed; lattice-hull vertex counts need not be monotone in the radius. -/
theorem scale_eventual_count {F : ℕ → ℕ} {a q K R₀ : ℕ}
    (ha : 0 < a) (hq : 0 < q) (hK : 0 < K)
    (hcount : ∀ R : ℕ, R₀ ≤ R → R^a ≤ K*(F R)^q) :
    ∃ C : ℕ, 0 < C ∧ ∀ b : ℕ, 0 < b → b^a ≤ F (C*b^q) := by
  let C := K+R₀+1
  have hC : 0 < C := by dsimp [C]; omega
  have hCK : K ≤ C^a :=
    (show K ≤ C by dsimp [C]; omega).trans (Nat.le_self_pow ha.ne' C)
  refine ⟨C,hC,?_⟩
  intro b hb
  have hbq : 0 < b^q := by positivity
  have hlarge : R₀ ≤ C*b^q :=
    (show R₀ ≤ C by dsimp [C]; omega).trans (Nat.le_mul_of_pos_right C hbq)
  have hp : K*(b^a)^q ≤ K*(F (C*b^q))^q := by
    calc
      _ ≤ (C*b^q)^a := by
        rw [mul_pow,← pow_mul,← pow_mul,Nat.mul_comm a q]
        exact Nat.mul_le_mul_right _ hCK
      _ ≤ _ := hcount _ hlarge
  have hp' : (b^a)^q ≤ (F (C*b^q))^q := Nat.le_of_mul_le_mul_left hp hK
  exact (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) hq.ne').mp hp'

/-- Real multiplicative constants may be rounded upward before the
integer radius scaling, without a monotonicity assumption on the count. -/
theorem scale_eventual_real_power {F : ℕ → ℕ} {a q R₀ : ℕ} {A : ℝ}
    (ha : 0 < a) (hq : 0 < q)
    (hcount : ∀ R : ℕ, R₀ ≤ R → (R : ℝ)^a ≤ A*(F R : ℝ)^q) :
    ∃ C : ℕ, 0 < C ∧ ∀ b : ℕ, 0 < b → b^a ≤ F (C*b^q) := by
  let K := Nat.ceil A + 1
  have hK : 0 < K := by dsimp [K]; omega
  have hAK : A ≤ (K : ℝ) := by
    have := Nat.le_ceil A
    dsimp [K]
    push_cast
    linarith
  apply scale_eventual_count ha hq hK
  intro R hR
  have hh := (hcount R hR).trans
    (mul_le_mul_of_nonneg_right hAK (by positivity : 0 ≤ (F R : ℝ)^q))
  exact_mod_cast hh

/-- The conventional eventual sharp real-power estimate implies exactly
the uniform integer count consumed by the graph theorem. -/
theorem scale_eventual_rpow {F : ℕ → ℕ} {a q R₀ : ℕ} {c : ℝ}
    (ha : 0 < a) (hq : 0 < q) (hc : 0 < c)
    (hcount : ∀ R : ℕ, R₀ ≤ R →
      c*(R : ℝ)^((a : ℝ)/q) ≤ F R) :
    ∃ C : ℕ, 0 < C ∧ ∀ b : ℕ, 0 < b → b^a ≤ F (C*b^q) := by
  apply scale_eventual_real_power (A := (c^q)⁻¹) ha hq
  intro R hR
  have hr : 0 ≤ (R : ℝ) := by positivity
  have hcq : 0 < c^q := pow_pos hc q
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hp := pow_le_pow_left₀ (mul_nonneg hc.le (Real.rpow_nonneg hr _)) (hcount R hR) q
  have he : ((R : ℝ)^((a : ℝ)/q))^q = (R : ℝ)^a := by
    rw [← Real.rpow_mul_natCast hr, div_mul_cancel₀ _ hq', Real.rpow_natCast]
  rw [mul_pow,he] at hp
  calc
    _ = (c^q)⁻¹*(c^q*(R : ℝ)^a) := by rw [← mul_assoc,inv_mul_cancel₀ hcq.ne',one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hcq.le)

end LinearDistancePreservers.LatticeScaling
