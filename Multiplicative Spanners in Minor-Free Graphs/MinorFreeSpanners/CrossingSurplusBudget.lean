import Mathlib.Tactic

/-! Numerical accounting for two opposite crossing-edge orientations.
No graph or cleaning theorem follows without the corresponding actual
common-neighbor and bad-pair incidence counts. -/
namespace MinorFreeSpanners

/-- The loss of a crossing fiber can be charged to ordered same-orientation
pairs, except for the literal one-plus-one bad-pair case. -/
theorem crossing_surplus_budget (p q : ℕ) :
    p+q-1 ≤ p*(p-1)+q*(q-1)+(if p=1 ∧ q=1 then 1 else 0) := by
  have hs : ∀ n : ℕ, n-1 ≤ n*(n-1) := by
    intro n
    by_cases hn : n=0
    · simp [hn]
    · simpa using Nat.mul_le_mul_right (n-1) (show 1 ≤ n by omega)
  by_cases hp : p=0
  · simp only [hp,Nat.zero_add,Nat.zero_mul,Nat.zero_sub,zero_ne_one,false_and,ite_false,Nat.add_zero]
    exact hs q
  by_cases hq : q=0
  · simp only [hq,Nat.add_zero,Nat.zero_sub,Nat.zero_mul,zero_ne_one,and_false,ite_false]
    exact hs p
  by_cases hp2 : 2 ≤ p
  · have h : p ≤ p*(p-1) := Nat.le_mul_of_pos_right p (by omega)
    have hh := hs q
    omega
  by_cases hq2 : 2 ≤ q
  · have h : q ≤ q*(q-1) := Nat.le_mul_of_pos_right q (by omega)
    have hh := hs p
    omega
  have hp1 : p=1 := by omega
  have hq1 : q=1 := by omega
  simp [hp1,hq1]

/-- The ordered-pair collision budget still fits the source clean coefficient
when the common-neighbor threshold is at least one. This is arithmetic only;
actual global collision and bad-pair bounds must be proved separately. -/
theorem ordered_collision_absorption (ell count : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    (ell:ℝ)*count + (ell*(ell-1):ℕ)*q*count ≤
      ell*q*((ell+1)*(count:ℝ)) := by
  by_cases he : ell=0
  · simp [he]
  have hel : 1 ≤ ell := by omega
  rw [Nat.cast_mul,Nat.cast_sub hel]
  push_cast
  have hn : 0 ≤ (ell:ℝ)*(2*q-1)*(count:ℝ) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (Nat.cast_nonneg _)
  nlinarith

end MinorFreeSpanners
