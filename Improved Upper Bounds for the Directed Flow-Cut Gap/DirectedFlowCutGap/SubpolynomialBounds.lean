import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Uniform subpolynomial envelopes for epoch bookkeeping

The constants in `Subpolynomial` are chosen after the exponent and before
the input size. All estimates apply to every positive natural size, with
finite exceptions absorbed into a constant. The functions themselves are
also defined at zero, without dividing by a zero logarithm.

These are analytic estimates only. No graph, sampling law, algorithmic
runtime, or rounding conclusion is postulated by this module.
-/

namespace DirectedFlowCutGap.SubpolynomialBounds

noncomputable section
open Filter
open scoped BigOperators Topology

/-- A uniform bound at every positive integer size, for every positive exponent. -/
def Subpolynomial (f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → |f n| ≤ C * (n : ℝ) ^ ε

namespace Subpolynomial

/-- Finite exceptions change the constant, not its quantifier order. -/
theorem of_eventually {f : ℕ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop, |f n| ≤ C * (n : ℝ) ^ ε) : Subpolynomial f := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := h ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  let S : ℝ := ∑ i ∈ Finset.range N, |f i|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C + S, by linarith, fun n hn => ?_⟩
  have hp : 1 ≤ (n : ℝ) ^ ε :=
    Real.one_le_rpow (by exact_mod_cast hn) hε.le
  by_cases hlarge : N ≤ n
  · exact (hN n hlarge).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hS) (Real.rpow_nonneg (Nat.cast_nonneg n) ε))
  · have hsmall : |f n| ≤ S :=
      Finset.single_le_sum (fun i _ => abs_nonneg (f i))
        (Finset.mem_range.mpr (Nat.lt_of_not_ge hlarge))
    exact hsmall.trans ((by linarith : S ≤ C + S).trans
      (le_mul_of_one_le_right (by linarith) hp))

theorem const (a : ℝ) : Subpolynomial (fun _ => a) := by
  intro ε hε
  refine ⟨|a| + 1, by positivity, fun n hn => ?_⟩
  have hp := Real.one_le_rpow (by exact_mod_cast hn : (1 : ℝ) ≤ n) hε.le
  exact (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
    (le_mul_of_one_le_right (by positivity) hp)

theorem mono {f g : ℕ → ℝ} (hg : Subpolynomial g)
    (hfg : ∀ n : ℕ, 1 ≤ n → |f n| ≤ |g n|) : Subpolynomial f := by
  intro ε hε
  obtain ⟨C, hC, hgC⟩ := hg ε hε
  exact ⟨C, hC, fun n hn => (hfg n hn).trans (hgC n hn)⟩

theorem add {f g : ℕ → ℝ} (hf : Subpolynomial f) (hg : Subpolynomial g) :
    Subpolynomial (fun n => f n + g n) := by
  intro ε hε
  obtain ⟨C, hC, hfC⟩ := hf ε hε
  obtain ⟨D, hD, hgD⟩ := hg ε hε
  refine ⟨C + D, add_pos hC hD, fun n hn => ?_⟩
  calc
    |f n + g n| ≤ |f n| + |g n| := abs_add_le _ _
    _ ≤ C * (n : ℝ) ^ ε + D * (n : ℝ) ^ ε := add_le_add (hfC n hn) (hgD n hn)
    _ = (C + D) * (n : ℝ) ^ ε := by ring

theorem mul {f g : ℕ → ℝ} (hf : Subpolynomial f) (hg : Subpolynomial g) :
    Subpolynomial (fun n => f n * g n) := by
  intro ε hε
  obtain ⟨C, hC, hfC⟩ := hf (ε / 2) (by linarith)
  obtain ⟨D, hD, hgD⟩ := hg (ε / 2) (by linarith)
  refine ⟨C * D, mul_pos hC hD, fun n hn => ?_⟩
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  calc
    |f n * g n| = |f n| * |g n| := abs_mul _ _
    _ ≤ (C * (n : ℝ) ^ (ε / 2)) * (D * (n : ℝ) ^ (ε / 2)) :=
      mul_le_mul (hfC n hn) (hgD n hn) (abs_nonneg _) (by positivity)
    _ = (C * D) * ((n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2)) := by ring
    _ = (C * D) * (n : ℝ) ^ ε := by rw [← Real.rpow_add hnpos]; congr 2; ring

theorem pow {f : ℕ → ℝ} (hf : Subpolynomial f) (k : ℕ) :
    Subpolynomial (fun n => f n ^ k) := by
  induction k with
  | zero => simpa using const 1
  | succ k ih => simpa [pow_succ] using ih.mul hf

theorem finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, Subpolynomial (f i)) :
    Subpolynomial (fun n => ∏ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 1
  | @insert i s hi ih =>
      simpa [Finset.prod_insert hi] using
        (hf i (Finset.mem_insert_self i s)).mul
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, Subpolynomial (f i)) :
    Subpolynomial (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 0
  | @insert i s hi ih =>
      simpa [Finset.sum_insert hi] using
        (hf i (Finset.mem_insert_self i s)).add
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- A smaller exponent absorbs any fixed prefactor at all sufficiently large sizes. -/
theorem eventually_le_rpow {f : ℕ → ℝ} (hf : Subpolynomial f)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ ε := by
  obtain ⟨C, _hC, hbound⟩ := hf (ε / 2) (by linarith)
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < ε / 2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop C, eventually_ge_atTop (1 : ℕ)] with n hlarge hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  calc
    |f n| ≤ C * (n : ℝ) ^ (ε / 2) := hbound n hn
    _ ≤ (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = (n : ℝ) ^ ε := by rw [← Real.rpow_add hnpos]; congr 1; ring

end Subpolynomial

/-- Safe restart shrink factor, also valid at size zero. -/
def r (n : ℕ) : ℝ := max 2 (Real.log ((n : ℝ) + 2))

/-- Conservative cap on positive geometric mass reductions. -/
def J (n : ℕ) : ℕ := Nat.ceil (3 * Real.log ((n : ℝ) + 2) / Real.log (r n))

/-- Uniform envelope for the factor-four cap progression. -/
def B (n : ℕ) : ℝ := 4 ^ J n

/-- Harmlessly padded logarithmic recursion depth. -/
def H (n : ℕ) : ℕ := 2 + Nat.ceil (Real.log ((n : ℝ) + 2) / Real.log 2)

theorem log_size_pos (n : ℕ) : 0 < Real.log ((n : ℝ) + 2) :=
  Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) n; linarith)

theorem two_le_r (n : ℕ) : 2 ≤ r n := le_max_left _ _

theorem log_size_le_r (n : ℕ) : Real.log ((n : ℝ) + 2) ≤ r n := le_max_right _ _

theorem r_pos (n : ℕ) : 0 < r n := lt_of_lt_of_le (by norm_num) (two_le_r n)

theorem one_lt_r (n : ℕ) : 1 < r n := lt_of_lt_of_le (by norm_num) (two_le_r n)

theorem log_r_pos (n : ℕ) : 0 < Real.log (r n) := Real.log_pos (one_lt_r n)

theorem log_two_le_log_r (n : ℕ) : Real.log 2 ≤ Real.log (r n) :=
  Real.log_le_log (by norm_num) (two_le_r n)

theorem ratio_nonneg (n : ℕ) : 0 ≤ 3 * Real.log ((n : ℝ) + 2) / Real.log (r n) :=
  div_nonneg (mul_nonneg (by norm_num) (log_size_pos n).le) (log_r_pos n).le

theorem ratio_le_J (n : ℕ) :
    3 * Real.log ((n : ℝ) + 2) / Real.log (r n) ≤ (J n : ℝ) := Nat.le_ceil _

theorem J_lt_ratio_add_one (n : ℕ) :
    (J n : ℝ) < 3 * Real.log ((n : ℝ) + 2) / Real.log (r n) + 1 :=
  Nat.ceil_lt_add_one (ratio_nonneg n)

theorem J_le_log_envelope (n : ℕ) :
    (J n : ℝ) ≤ (3 / Real.log 2) * Real.log ((n : ℝ) + 2) + 1 := by
  have hdiv : 3 * Real.log ((n : ℝ) + 2) / Real.log (r n) ≤
      3 * Real.log ((n : ℝ) + 2) / Real.log 2 :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (log_size_pos n).le)
      (Real.log_pos (by norm_num)) (log_two_le_log_r n)
  have := (J_lt_ratio_add_one n).le
  calc
    (J n : ℝ) ≤ 3 * Real.log ((n : ℝ) + 2) / Real.log 2 + 1 := by linarith
    _ = (3 / Real.log 2) * Real.log ((n : ℝ) + 2) + 1 := by ring

theorem one_le_B (n : ℕ) : 1 ≤ B n := one_le_pow₀ (by norm_num)

theorem B_pos (n : ℕ) : 0 < B n := lt_of_lt_of_le zero_lt_one (one_le_B n)

theorem four_pow_le_B {n k : ℕ} (hk : k ≤ J n) : (4 : ℝ) ^ k ≤ B n :=
  pow_le_pow_right₀ (by norm_num) hk

theorem cap_scale_le {n k : ℕ} {b₀ : ℝ} (hk : k ≤ J n) (hb₀ : 0 ≤ b₀) :
    (4 : ℝ) ^ k * b₀ ≤ B n * b₀ := mul_le_mul_of_nonneg_right (four_pow_le_B hk) hb₀

/-- Convert the exact geometric mass bound to the chosen integer restart envelope. -/
theorem restart_count_le_J {n k : ℕ} (hn : 1 ≤ n)
    (hpow : r n ^ k ≤ (n : ℝ) ^ (3 : ℕ)) : k ≤ J n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hlog := Real.log_le_log (pow_pos (r_pos n) k) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  have hsize : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log hnpos (by linarith)
  have hk : (k : ℝ) ≤ 3 * Real.log ((n : ℝ) + 2) / Real.log (r n) :=
    (le_div_iff₀ (log_r_pos n)).mpr (by norm_num at hlog; nlinarith)
  exact_mod_cast hk.trans (ratio_le_J n)

/-- The ceiling is also large enough to dominate the padded cubic mass bound. -/
theorem cubic_le_restart_power (n : ℕ) : ((n : ℝ) + 2) ^ (3 : ℕ) ≤ r n ^ J n := by
  apply (Real.le_pow_iff_log_le (by positivity) (r_pos n)).mpr
  rw [Real.log_pow]
  norm_num
  exact (div_le_iff₀ (log_r_pos n)).mp (ratio_le_J n)

/-- Also supplies strict power thresholds used by finite restart executions. -/
theorem cubic_lt_next_restart_power (n : ℕ) :
    (n : ℝ) ^ (3 : ℕ) < r n ^ (J n + 1) := by
  have hsmall : (n : ℝ) ^ (3 : ℕ) < ((n : ℝ) + 2) ^ (3 : ℕ) := by
    have := Nat.cast_nonneg (α := ℝ) n
    nlinarith [sq_nonneg (n : ℝ)]
  exact hsmall.trans_le ((cubic_le_restart_power n).trans
    (pow_le_pow_right₀ (one_lt_r n).le (Nat.le_succ (J n))))

theorem two_le_H (n : ℕ) : 2 ≤ H n := Nat.le_add_right _ _

theorem H_add_one_le_log_envelope (n : ℕ) :
    (H n : ℝ) + 1 ≤ (1 / Real.log 2) * Real.log ((n : ℝ) + 2) + 4 := by
  have hc := (Nat.ceil_lt_add_one
    (div_nonneg (log_size_pos n).le (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)).le
  dsimp [H]
  push_cast
  have heq : Real.log ((n : ℝ) + 2) / Real.log 2 =
      (1 / Real.log 2) * Real.log ((n : ℝ) + 2) := by ring
  rw [heq] at hc ⊢
  linarith

theorem shifted_rpow_le {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 ≤ ε) :
    ((n : ℝ) + 2) ^ ε ≤ (3 : ℝ) ^ ε * (n : ℝ) ^ ε := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    ((n : ℝ) + 2) ^ ε ≤ (3 * (n : ℝ)) ^ ε :=
      Real.rpow_le_rpow (by positivity) (by linarith) hε
    _ = (3 : ℝ) ^ ε * (n : ℝ) ^ ε := Real.mul_rpow (by norm_num) (Nat.cast_nonneg n)

theorem log_size_subpolynomial : Subpolynomial (fun n => Real.log ((n : ℝ) + 2)) := by
  intro ε hε
  refine ⟨(3 : ℝ) ^ ε / ε, by positivity, fun n hn => ?_⟩
  rw [abs_of_pos (log_size_pos n)]
  calc
    Real.log ((n : ℝ) + 2) ≤ ((n : ℝ) + 2) ^ ε / ε :=
      Real.log_le_rpow_div (by positivity) hε
    _ ≤ ((3 : ℝ) ^ ε * (n : ℝ) ^ ε) / ε :=
      div_le_div_of_nonneg_right (shifted_rpow_le hn hε.le) hε.le
    _ = ((3 : ℝ) ^ ε / ε) * (n : ℝ) ^ ε := by ring

theorem r_subpolynomial : Subpolynomial r := by
  apply ((Subpolynomial.const 2).add log_size_subpolynomial).mono
  intro n _
  have hlog := log_size_pos n
  rw [abs_of_pos (r_pos n), abs_of_pos (by linarith :
    0 < 2 + Real.log ((n : ℝ) + 2))]
  exact max_le (by linarith [log_size_pos n]) (by linarith)

theorem J_add_one_subpolynomial : Subpolynomial (fun n => (J n : ℝ) + 1) := by
  apply (((Subpolynomial.const (3 / Real.log 2)).mul log_size_subpolynomial).add
    (Subpolynomial.const 2)).mono
  intro n _
  have hlog := (log_size_pos n).le
  have hlogtwo := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  linarith [J_le_log_envelope n]

theorem H_add_one_subpolynomial : Subpolynomial (fun n => (H n : ℝ) + 1) := by
  apply (((Subpolynomial.const (1 / Real.log 2)).mul log_size_subpolynomial).add
    (Subpolynomial.const 4)).mono
  intro n _
  have hlog := (log_size_pos n).le
  have hlogtwo := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  exact H_add_one_le_log_envelope n

theorem tendsto_log_r : Tendsto (fun n => Real.log (r n)) atTop atTop := by
  have hs : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀ n : ℕ, (n : ℝ) ≤ (n : ℝ) + 2)
      tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono (fun n =>
    Real.log_le_log (log_size_pos n) (log_size_le_r n))
  exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hs)

/-- The factor-four cap is controlled by every positive power of the padded size.
The threshold follows from the proved divergence of `log (r n)`. -/
theorem B_eventually_le_shifted_rpow {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, B n ≤ 4 * ((n : ℝ) + 2) ^ ε := by
  filter_upwards [tendsto_log_r.eventually_ge_atTop (3 * Real.log 4 / ε)] with n hn
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hcoeff : 3 * Real.log 4 / Real.log (r n) ≤ ε := by
    apply (div_le_iff₀ (log_r_pos n)).mpr
    have := (div_le_iff₀ hε).mp hn
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hcoeff (log_size_pos n).le
  have hceil := mul_le_mul_of_nonneg_right (J_lt_ratio_add_one n).le hlog4.le
  have hbound : (J n : ℝ) * Real.log 4 ≤ Real.log 4 + ε * Real.log ((n : ℝ) + 2) := by
    have heq : (3 * Real.log ((n : ℝ) + 2) / Real.log (r n) + 1) * Real.log 4 =
        (3 * Real.log 4 / Real.log (r n)) * Real.log ((n : ℝ) + 2) + Real.log 4 := by ring
    rw [heq] at hceil
    linarith
  apply (Real.log_le_log_iff (B_pos n) (by positivity)).mp
  rw [B, Real.log_pow, Real.log_mul (by norm_num) (by positivity),
    Real.log_rpow (by positivity)]
  exact hbound

theorem B_subpolynomial : Subpolynomial B := by
  apply Subpolynomial.of_eventually
  intro ε hε
  refine ⟨4 * (3 : ℝ) ^ ε, by positivity, ?_⟩
  filter_upwards [B_eventually_le_shifted_rpow hε, eventually_ge_atTop (1 : ℕ)] with n hB hn
  rw [abs_of_pos (B_pos n)]
  calc
    B n ≤ 4 * ((n : ℝ) + 2) ^ ε := hB
    _ ≤ 4 * ((3 : ℝ) ^ ε * (n : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (shifted_rpow_le hn hε.le) (by norm_num)
    _ = (4 * (3 : ℝ) ^ ε) * (n : ℝ) ^ ε := by ring

/-- Fixed degrees may be selected later by graph and probability interfaces. -/
theorem parameter_product_subpolynomial (a b c d : ℕ) :
    Subpolynomial (fun n => B n ^ a * r n ^ b * ((J n : ℝ) + 1) ^ c *
      ((H n : ℝ) + 1) ^ d) :=
  (((B_subpolynomial.pow a).mul (r_subpolynomial.pow b)).mul
    (J_add_one_subpolynomial.pow c)).mul (H_add_one_subpolynomial.pow d)

/-- Logarithmic union-bound factors with any fixed polynomial event count. -/
theorem log_union_bound_subpolynomial (q : ℕ) :
    Subpolynomial (fun n => Real.log (((J n : ℝ) + 1) * ((n : ℝ) + 2) ^ q) + 1) := by
  apply (J_add_one_subpolynomial.add
    ((Subpolynomial.const (q : ℝ)).mul log_size_subpolynomial)).mono
  intro n _
  have hJ : (0 : ℝ) < (J n : ℝ) + 1 := by positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hlogJ : 0 ≤ Real.log ((J n : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (J n); linarith)
  have hq : 0 ≤ (q : ℝ) * Real.log ((n : ℝ) + 2) :=
    mul_nonneg (Nat.cast_nonneg q) (log_size_pos n).le
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by positivity)]
  have hupper := Real.log_le_sub_one_of_pos hJ
  linarith

/-- The witness hard-regime cap holds eventually, with every positive exponent. -/
theorem eventually_sixtyfour_B_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 64 * B n ≤ (n : ℝ) ^ ε := by
  have h := ((Subpolynomial.const 64).mul B_subpolynomial).eventually_le_rpow hε
  filter_upwards [h] with n hn
  simpa only [abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 64) (B_pos n))] using hn

theorem eventually_sixtyfour_B_le_cuberoot :
    ∀ᶠ n : ℕ in atTop, 64 * B n ≤ (n : ℝ) ^ ((1 : ℝ) / 3) :=
  eventually_sixtyfour_B_le_rpow (by norm_num)

/-- A positive threshold can be selected before the graph size. -/
theorem exists_hard_regime_threshold {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → 64 * B n ≤ (n : ℝ) ^ ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_sixtyfour_B_le_rpow hε)
  exact ⟨max N 1, le_max_right _ _, fun n hn => hN n ((le_max_left _ _).trans hn)⟩

end
end DirectedFlowCutGap.SubpolynomialBounds
