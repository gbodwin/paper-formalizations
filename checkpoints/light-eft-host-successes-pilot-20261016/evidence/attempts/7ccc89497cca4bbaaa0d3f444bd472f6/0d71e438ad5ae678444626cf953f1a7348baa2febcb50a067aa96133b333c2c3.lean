import LightSpanners.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Auxiliary steps for §5. These do NOT assert that bucket paths satisfy
dispersion or the counting lemma: those are remaining obligations. -/
namespace LightSpanners
open Finset

/-- Endpoint injectivity gives the n² cap. Proving injectivity for the
paper's bucket-monotone safe paths is still required. -/
theorem endpoint_count {P V : Type*} [Fintype P] [Fintype V]
    (endpoints : P → V × V) (h : Function.Injective endpoints) :
    Fintype.card P ≤ Fintype.card V * Fintype.card V := by
  simpa using Fintype.card_le_of_injective endpoints h

/-- Exact dyadic sum, with bucket indices beginning at zero. -/
theorem dyadic_sum (j : ℕ) :
    (∑ i ∈ range (j+1), (2 : ℝ)^i) = 2^(j+1)-1 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [sum_range_succ, ih, pow_succ]
    ring

/-- The two-prefix cycle-edge budget in Lemma 5.5. -/
theorem bucket_budget (eps k : ℝ) (heps : 0 < eps) (hk : 0 < k) (j : ℕ) :
    4 * eps * k * (∑ i ∈ range (j+1), (2 : ℝ)^i) < 8 * eps * k * 2^j := by
  rw [dyadic_sum, pow_succ]
  nlinarith [mul_pos heps hk]

/-- The normalized-weight contradiction after extracting the cycle.
Its existence and combinatorial budget hypotheses are NOT discharged here. -/
theorem dispersion_arithmetic (eps k W cyc noncyc unit : ℝ)
    (hW : 0 < W) (hsplit : cyc ≤ noncyc + unit)
    (hnoncyc : noncyc ≤ 2*k*W) (hunit : unit < 8*eps*k*W) :
    cyc / W < (1+4*eps)*2*k := by
  apply (div_lt_iff₀ hW).2
  nlinarith

/-- The final comparison of lower and upper path counts. -/
theorem counting_sandwich (n p a : ℝ) (k : ℕ) (hn : 0 < n)
    (lower : n*a^k ≤ p) (upper : p ≤ n*n) : a^k ≤ n := by
  nlinarith

/-- Algebraic bootstrap in Lemma 5.13, given the expectation estimate.
Independent sampling and the medium lemma remain separate obligations. -/
theorem sampling_bootstrap (c n p q expected : ℝ) (k : ℕ)
    (hq : 0 < q) (lower : c*n ≤ expected) (identity : expected = p*q^k) :
    c*n / q^k ≤ p := by
  apply (div_le_iff₀ (pow_pos hq k)).2
  nlinarith

/-- Exact reparameterization from target stretch to the girth threshold. -/
theorem stretch_reparameterization (eps : ℝ) (k : ℕ) (hk : 0 < k) :
    (1 + 4 * (eps * (2*(k:ℝ)-1) / (8*(k:ℝ)))) * (2*(k:ℝ)) =
      (1+eps)*(2*(k:ℝ)-1)+1 := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  field_simp
  ring

/-- Positive rescaling preserves normalized cycle weights. -/
theorem normalized_scale (scale total maxWeight : ℝ) (hs : 0 < scale) :
    (scale*total)/(scale*maxWeight) = total/maxWeight := by
  exact mul_div_mul_left total maxWeight (ne_of_gt hs)
end LightSpanners
