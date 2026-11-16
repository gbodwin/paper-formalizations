import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! Explicit finite-order and uniform-epsilon arithmetic for the lower bound
at competition parameters at most 2f-1. -/
namespace LightEFTSpanners.CorrectedLowCompetition

theorem large_cycle_quotient {n f : ℕ} {t : ℝ} (ht : 1≤t)
    (hn : (2*⌈t⌉₊+1)*(f+1)≤n) :
    3≤n/(f+1) ∧ 2*⌈t⌉₊≤(n/(f+1)-3)+2 := by
  have hceil : 0<⌈t⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have hquot := (Nat.le_div_iff_mul_le (by omega : 0<f+1)).mpr hn
  omega

theorem quotient_order_half {n b : ℕ} (hb : 0<b) (hn : 1≤n/b) :
    n≤2*(n/b*b) := by
  have hmod := Nat.mod_lt n hb
  have hdiv := Nat.div_add_mod n b
  have hbase := Nat.mul_le_mul_right b hn
  simp only [one_mul,Nat.mul_comm b (n/b)] at hdiv hbase
  omega

theorem small_order_ratio_le_one {n f : ℕ} {t : ℝ} (hf : 1≤f) (ht : 1≤t)
    (hn : ¬(2*⌈t⌉₊+1)*(f+1)≤n) : (n:ℝ)/(32*(f:ℝ)^2*t)≤1 := by
  have hfR : (1:ℝ)≤f := by exact_mod_cast hf
  have htpos : 0<t := by linarith
  have hceil : (⌈t⌉₊:ℝ)≤2*t := by
    have h := Nat.ceil_lt_add_one htpos.le
    linarith
  have hnR : (n:ℝ)<(2*(⌈t⌉₊:ℝ)+1)*((f:ℝ)+1) := by
    exact_mod_cast (lt_of_not_ge hn)
  have hA : 2*(⌈t⌉₊:ℝ)+1≤5*t := by linarith
  have hB : (f:ℝ)+1≤2*f := by linarith
  have hprod := mul_le_mul hA hB (by positivity : (0:ℝ)≤(f:ℝ)+1)
    (by positivity : (0:ℝ)≤5*t)
  have hff : (f:ℝ)≤(f:ℝ)^2 := by nlinarith
  have hffmul := mul_le_mul_of_nonneg_right hff (by positivity : (0:ℝ)≤32*t)
  have hft : 0≤(f:ℝ)*t := by positivity
  apply (div_le_one (by positivity : (0:ℝ)<32*(f:ℝ)^2*t)).mpr
  nlinarith

def introStretch (k : ℕ) (eps : ℝ) : ℝ := (1+eps)*(2*(k:ℝ)-1)

theorem introStretch_bounds {k : ℕ} {eps : ℝ} (hk : 1≤k) (heps : 0<eps)
    (hsmall : eps≤1/(k:ℝ)) : 1 ≤ introStretch k eps ∧ introStretch k eps≤3*(k:ℝ) := by
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hkpos : (0:ℝ)<k := by linarith
  have hmul := (le_div_iff₀ hkpos).mp hsmall
  have hprod : 0≤eps*(2*(k:ℝ)-1) := mul_nonneg heps.le (by linarith)
  constructor <;> unfold introStretch <;> nlinarith

end LightEFTSpanners.CorrectedLowCompetition
