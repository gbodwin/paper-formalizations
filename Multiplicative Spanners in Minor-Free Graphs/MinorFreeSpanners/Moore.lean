import MinorFreeSpanners.Greedy
import VFTSpanners.Moore
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Theorem 11 is obtained from the already proved graph-level Moore bound,
not a new axiom. The exact power form makes its uniform constant explicit. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem theorem11_power (G : SimpleGraph V) (k : ℕ) (hk : 1 ≤ k)
    (hg : GirthAbove G (2*k)) :
    G.edgeFinset.card^k ≤ 2^k * (Fintype.card V)^(k+1) :=
  VFTSpanners.moore_edge_bound G k hk hg

/-- Standard O(n^(1+1/k)) form with uniform constant 2. -/
theorem theorem11 (G : SimpleGraph V) (k : ℕ) (hk : 1 ≤ k)
    (hg : GirthAbove G (2*k)) :
    (G.edgeFinset.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) ^ (1 + 1/(k:ℝ)) := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hpow : (G.edgeFinset.card:ℝ)^k ≤ (2:ℝ)^k*(Fintype.card V:ℝ)^(k+1) := by
    exact_mod_cast theorem11_power G k hk hg
  have hh := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg _) _)
    hpow (inv_nonneg.mpr hkpos.le)
  rw [Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) (by omega),
    Real.mul_rpow (by positivity) (by positivity),
    Real.pow_rpow_inv_natCast (by norm_num) (by omega)] at hh
  have he : ((k+1:ℕ):ℝ) * (k:ℝ)⁻¹ = 1+1/(k:ℝ) := by
    push_cast
    field_simp
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), he] at hh
  exact hh

end MinorFreeSpanners
