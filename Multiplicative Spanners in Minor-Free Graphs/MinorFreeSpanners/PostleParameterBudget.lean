import MinorFreeSpanners.CoreParameters

/-! Parameter arithmetic for the actual technical density-increment
construction. These statements supply no graph-existence hypothesis. -/
namespace MinorFreeSpanners

theorem postle_ceil_sixth_bounds (k : ℕ) (hk : 100 ≤ k) :
    (k:ℝ)/6 ≤ (⌈(k:ℝ)/6⌉₊:ℝ) ∧ (⌈(k:ℝ)/6⌉₊:ℝ) ≤ (k:ℝ)/5 := by
  have hkR : (100:ℝ) ≤ k := by exact_mod_cast hk
  have hc := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ (k:ℝ)/6)
  exact ⟨Nat.le_ceil _,by linarith⟩

/-- The actual hypothesis needed for Theorem 3.6 is d0>=ell², rather than
the unnecessarily stronger d0>=k² printed in Postle v3 page 8. -/
theorem postle_bipartite_density_budget (k : ℕ) (hk : 100 ≤ k) (d : ℝ)
    (hd : (k:ℝ)^2 ≤ d) :
    d/2 ≤ (1-6/(k:ℝ))*d ∧
      (⌈(k:ℝ)/6⌉₊:ℝ)^2 ≤ (1-6/(k:ℝ))*d := by
  have hkR : (100:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hd0 : 0 ≤ d := (sq_nonneg _).trans hd
  have hi : (6:ℝ)/k ≤ 1/2 := (div_le_iff₀ hk0).mpr (by linarith)
  have hhalf : d/2 ≤ (1-6/(k:ℝ))*d := by nlinarith
  have he := (postle_ceil_sixth_bounds k hk).2
  have he0 : (0:ℝ) ≤ (⌈(k:ℝ)/6⌉₊:ℝ) := Nat.cast_nonneg _
  have he2 := mul_le_mul he he he0 (by positivity : (0:ℝ) ≤ (k:ℝ)/5)
  constructor
  · exact hhalf
  · nlinarith

/-- The first small-dense alternative has the coefficient 1/(2k²).
The printed proof writes 1/(2k) at one equality, but uses the correct
k² denominator in the resulting d/(24k⁶) density target. -/
theorem postle_first_edge_coefficient (k d : ℝ) :
    (1/k)*(1/k)*d^2/2 = d^2/(2*k^2) := by ring

end MinorFreeSpanners
