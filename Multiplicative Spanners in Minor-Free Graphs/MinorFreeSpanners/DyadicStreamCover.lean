import MinorFreeSpanners.FiniteGeometricStreamBound
import Mathlib.Algebra.Order.Archimedean.Basic

/-! An arbitrary scale multiplier is covered by finitely many integer-start
geometric streams. Dyadic starting scales avoid an unproved base-state oracle. -/
namespace MinorFreeSpanners

 theorem exists_dyadic_stream_band (t x : ℝ) (ell N : ℕ)
    (ht : 1<t) (hx : t≤x) (hcut : x<t^(N+1)) (hell : t≤(2:ℝ)^ell) :
    ∃ j<ell,∃ k<N,t^(k+1)*(2:ℝ)^j≤x ∧ x≤2*(t^(k+1)*(2:ℝ)^j) := by
  have ht0 : 0<t := by linarith only [ht]
  obtain ⟨q,hlo,hhi⟩ := exists_nat_pow_near (show 1≤x by linarith only [ht,hx]) ht
  have hq : q≠0 := by
    intro he
    subst q
    simp only [zero_add,pow_one] at hhi
    exact (not_lt_of_ge hx) hhi
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  have hk : k<N := by
    have h := (pow_lt_pow_iff_right₀ ht).mp (hlo.trans_lt hcut)
    omega
  have hp : 0<t^(k+1) := pow_pos ht0 _
  have hratio : 1≤x/t^(k+1) := (le_div_iff₀ hp).mpr (by simpa only [one_mul] using hlo)
  have hratioT : x/t^(k+1)<t := by
    apply (div_lt_iff₀ hp).mpr
    simpa only [pow_succ,mul_comm] using hhi
  obtain ⟨j,hjlo,hjhi⟩ := exists_nat_pow_near hratio (show (1:ℝ)<2 by norm_num)
  have hj : j<ell := (pow_lt_pow_iff_right₀ (show (1:ℝ)<2 by norm_num)).mp
    (hjlo.trans_lt (hratioT.trans_le hell))
  have low := (le_div_iff₀ hp).mp hjlo
  have high := (div_lt_iff₀ hp).mp hjhi
  refine ⟨j,hj,k,hk,?_,?_⟩
  · simpa only [mul_comm] using low
  · rw [pow_succ] at high
    nlinarith only [high]

end MinorFreeSpanners
