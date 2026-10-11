import MinorFreeSpanners.BipartiteDensityIncrement
import MinorFreeSpanners.ResidualMinorDensityAlgebra

/-! Explicit natural degree and imbalance parameters for joining the actual
core bipartite branch to the previously proved finite bipartite increment. -/
namespace MinorFreeSpanners

/-- Rounding up half the real density is supported by the proved bipartite
left degree. All padding and rounding loss is included in the inequalities. -/
theorem general_increment_rounded_degree (k : ℕ) (d : ℝ)
    (hk : 16 ≤ k) (hd : (k:ℝ)^3 ≤ d) :
    let D := ⌈d/2⌉₊
    (k:ℝ) ≤ D ∧ d/2 ≤ (D:ℝ) ∧ (D:ℝ) ≤ d ∧
      (D:ℝ) ≤ d-(2+3*(k:ℝ))*(1/(k:ℝ)^2)*d := by
  have hkR : (16:ℝ) ≤ k := by exact_mod_cast hk
  have hp : (0:ℝ) < k := by linarith
  have hk2 : (16:ℝ)^2 ≤ (k:ℝ)^2 := by nlinarith
  have hd4 : 4 ≤ d := by nlinarith [mul_nonneg (show (0:ℝ) ≤ k by positivity) (show 0 ≤ (k:ℝ)^2-256 by linarith)]
  have hdk : 2*(k:ℝ) ≤ d := by nlinarith [mul_nonneg (show (0:ℝ) ≤ k by positivity) (show 0 ≤ (k:ℝ)^2-2 by linarith)]
  have hlo : d/2 ≤ (⌈d/2⌉₊:ℝ) := Nat.le_ceil _
  have hhi : (⌈d/2⌉₊:ℝ) < d/2+1 := Nat.ceil_lt_add_one (by linarith)
  have hquarter : (2+3*(k:ℝ))*(1/(k:ℝ)^2) ≤ 1/4 := by
    rw [mul_one_div]
    apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
    nlinarith
  have hscale := mul_le_mul_of_nonneg_right hquarter (show 0 ≤ d by linarith)
  exact ⟨by linarith,hlo,by linarith,by linarith⟩

/-- The genuine natural imbalance k/4 fits both constructions and retains
at least k/8 in the old (ell-1) density multiplier. -/
theorem general_increment_imbalance (k : ℕ) (hk : 16 ≤ k) :
    1 ≤ k/4 ∧ 4*(k/4) ≤ k ∧ k/4+1 ≤ k ∧
      (k:ℝ)/8 ≤ (k/4:ℕ)-1 := by
  have hmod := Nat.mod_lt k (show 0<4 by omega)
  have hdiv := Nat.div_add_mod k 4
  have hlo : k ≤ 4*(k/4)+3 := by omega
  have hkR : (16:ℝ) ≤ k := by exact_mod_cast hk
  have hloR : (k:ℝ) ≤ 4*(k/4:ℕ)+3 := by exact_mod_cast hlo
  exact ⟨by omega,by omega,by omega,by linarith⟩

end MinorFreeSpanners
