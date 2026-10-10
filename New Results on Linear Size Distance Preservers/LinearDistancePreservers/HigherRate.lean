import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! General quantitative Behrend substitution and exact conversion from
integer-power bounds to the displayed fractional-power rate. This analytic
module does not assume or assert a sharp lattice vertex-count theorem. -/
namespace LinearDistancePreservers.HigherRate

/-- Substitute the terminal-scale inequalities into an arbitrary
integer-power capacity bound. -/
theorem real_product_rate {N T M Q E K a e q D : ℕ}
    (hT : T ≤ 4*M)
    (hQ : (T : ℝ)*Real.exp (-4*Real.sqrt (Real.log T)) ≤ 12*(Q : ℝ))
    (hE : M^a*Q^e*N^q ≤ K*E^D) :
    (T : ℝ)^(a+e)*(N : ℝ)^q*(Real.exp (-4*Real.sqrt (Real.log T)))^e ≤
      ((4^a*12^e*K : ℕ) : ℝ)*(E : ℝ)^D := by
  have ht : (T : ℝ) ≤ 4*(M : ℝ) := by exact_mod_cast hT
  have he : (M : ℝ)^a*(Q : ℝ)^e*(N : ℝ)^q ≤ (K : ℝ)*(E : ℝ)^D := by exact_mod_cast hE
  calc
    _ = (T : ℝ)^a*((T : ℝ)*Real.exp (-4*Real.sqrt (Real.log T)))^e*(N : ℝ)^q := by
      rw [pow_add,mul_pow]; ring
    _ ≤ (4*(M : ℝ))^a*(12*(Q : ℝ))^e*(N : ℝ)^q := by gcongr
    _ = (4 : ℝ)^a*12^e*((M : ℝ)^a*(Q : ℝ)^e*(N : ℝ)^q) := by simp only [mul_pow]; ring
    _ ≤ (4 : ℝ)^a*12^e*((K : ℝ)*(E : ℝ)^D) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by push_cast; ring

/-- A path covers all small-terminal cases with a dimension-dependent
coefficient whenever the vertex exponent does not exceed the power. -/
theorem small_path_rate {N T p q e D : ℕ} (hT : 2 ≤ T) (hTN : T ≤ N)
    (hlarge : ¬6 ≤ T) (hqD : q ≤ D) :
    (T : ℝ)^p*(N : ℝ)^q*(Real.exp (-4*Real.sqrt (Real.log T)))^e ≤
      ((5^p*2^D : ℕ) : ℝ)*((N-1 : ℕ) : ℝ)^D := by
  have hT5 : (T : ℝ) ≤ 5 := by exact_mod_cast (show T ≤ 5 by omega)
  have hN : (N : ℝ) ≤ 2*((N-1 : ℕ) : ℝ) := by exact_mod_cast (show N ≤ 2*(N-1) by omega)
  have hpow : (N : ℝ)^q ≤ (N : ℝ)^D := by
    exact_mod_cast (Nat.pow_le_pow_right (by omega : 1 ≤ N) hqD)
  have hloss : Real.exp (-4*Real.sqrt (Real.log T)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := Real.sqrt_nonneg (Real.log T); linarith)
  calc
    _ ≤ (5 : ℝ)^p*(N : ℝ)^q*1 := by
      gcongr
      simpa using pow_le_pow_left₀ (by positivity) hloss e
    _ ≤ (5 : ℝ)^p*(N : ℝ)^D := by
      simpa using mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ 5^p)
    _ ≤ (5 : ℝ)^p*(2*((N-1 : ℕ) : ℝ))^D := by gcongr
    _ = _ := by rw [mul_pow]; push_cast; ring

/-- A literal real-power rate from the integer-power formulation.
Using K itself rather than its D-th root keeps the coefficient integral. -/
theorem rate_of_power {N T E K p q e D : ℕ} (hD : D ≠ 0)
    (h : (T : ℝ)^p*(N : ℝ)^q*(Real.exp (-4*Real.sqrt (Real.log T)))^e ≤
      (K : ℝ)*(E : ℝ)^D) :
    (N : ℝ)^((q : ℝ)/D)*(T : ℝ)^((p : ℝ)/D)*
      Real.exp (-(4*(e : ℝ)/D)*Real.sqrt (Real.log T)) ≤ (K : ℝ)*(E : ℝ) := by
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have hn : ((N : ℝ)^((q : ℝ)/D))^D = (N : ℝ)^q := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N),div_mul_cancel₀ _ hDr,Real.rpow_natCast]
  have ht : ((T : ℝ)^((p : ℝ)/D))^D = (T : ℝ)^p := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg T),div_mul_cancel₀ _ hDr,Real.rpow_natCast]
  have hK : (K : ℝ) ≤ (K : ℝ)^D := by exact_mod_cast (Nat.le_self_pow hD K)
  have he := h.trans (mul_le_mul_of_nonneg_right hK (by positivity))
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) hD).mp
  rw [mul_pow,mul_pow,hn,ht,← Real.exp_nat_mul,mul_pow]
  have hh : (D : ℝ)*(-(4*(e : ℝ)/D)*Real.sqrt (Real.log T)) =
      (e : ℝ)*(-4*Real.sqrt (Real.log T)) := by field_simp
  rw [hh,Real.exp_nat_mul]
  simpa [mul_assoc,mul_comm,mul_left_comm] using he


/-- The paper's literal dimension-dependent exponents, with the loss
weakened from log T to log N. -/
theorem dimension_rate {N T E K d : ℕ} (hd : 1 ≤ d) (hT : 0 < T) (hTN : T ≤ N)
    (h : (T : ℝ)^(d*(d-1)+(d^2-1))*(N : ℝ)^(2*d)*
      (Real.exp (-4*Real.sqrt (Real.log T)))^(d^2-1) ≤
      (K : ℝ)*(E : ℝ)^(d*(d+1))) :
    (N : ℝ)^((2 : ℝ)/(d+1)) *
      (T : ℝ)^((((2*d+1)*(d-1) : ℕ) : ℝ)/((d*(d+1) : ℕ) : ℝ)) *
      Real.exp (-(4*((d-1 : ℕ) : ℝ)/d)*Real.sqrt (Real.log N)) ≤ (K : ℝ)*(E : ℝ) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hd1 : (d : ℝ)+1 ≠ 0 := by positivity
  have hds : 1 ≤ d^2 := by nlinarith
  have hs1 := Nat.sub_add_cancel hd
  have hs2 := Nat.sub_add_cancel hds
  have hp : d*(d-1)+(d^2-1)=(2*d+1)*(d-1) := by nlinarith
  have he : d^2-1=(d-1)*(d+1) := by nlinarith
  have hnexp : ((2*d : ℕ) : ℝ)/((d*(d+1) : ℕ) : ℝ) = (2 : ℝ)/(d+1) := by
    push_cast
    field_simp
  have heexp : 4*((d^2-1 : ℕ) : ℝ)/((d*(d+1) : ℕ) : ℝ) = 4*((d-1 : ℕ) : ℝ)/d := by
    rw [he]
    push_cast
    field_simp
  have hr := rate_of_power (N := N) (T := T) (E := E) (K := K)
    (by positivity : d*(d+1) ≠ 0) h
  rw [hp,hnexp,heexp] at hr
  have hlog : Real.log (T : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by exact_mod_cast hT) (by exact_mod_cast hTN)
  have hloss : Real.exp (-(4*((d-1 : ℕ) : ℝ)/d)*Real.sqrt (Real.log N)) ≤
      Real.exp (-(4*((d-1 : ℕ) : ℝ)/d)*Real.sqrt (Real.log T)) := by
    apply Real.exp_le_exp.mpr
    have hsq := Real.sqrt_le_sqrt hlog
    have hcoef : 0 ≤ 4*((d-1 : ℕ) : ℝ)/d := by positivity
    nlinarith
  exact (mul_le_mul_of_nonneg_left hloss (by positivity)).trans hr

end LinearDistancePreservers.HigherRate
