import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic

/-!
# Finite independent sampling and minimum-cost amplification

The experiment is the normalized product PMF on `Fin T → A`. Its output is
one of the actual samples, chosen to minimize cost. Finite Markov's inequality
and the product formula give failure at most `2⁻ᵀ`; an explicit logarithmic
sample count gives polynomially small failure. The input is a generic finite
law with an expected-cost bound and a validity predicate. Establishing those
hypotheses for an algorithm, and bounding its running time, remain separate.
-/

namespace DirectedFlowCutGap.FiniteAmplification

noncomputable section

open scoped BigOperators ENNReal Classical

variable {A : Type*} [Fintype A]

/-- The probability of an event, as a real number. No sigma-algebra is needed
on the finite outcome type. -/
def probability (p : PMF A) (P : A → Prop) : ℝ :=
  (p.toOuterMeasure {a | P a}).toReal

/-- The event probability is exactly its finite sum of atom masses. -/
theorem probability_eq_sum (p : PMF A) (P : A → Prop) :
    probability p P = ∑ a, if P a then (p a).toReal else 0 := by
  unfold probability
  rw [PMF.toOuterMeasure_apply_fintype]
  rw [ENNReal.toReal_sum (fun a _ => by
    by_cases h : P a <;> simp [Set.indicator, h, p.apply_ne_top a])]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : P a <;> simp [Set.indicator, h]

omit [Fintype A] in
theorem probability_nonneg (p : PMF A) (P : A → Prop) :
    0 ≤ probability p P := ENNReal.toReal_nonneg

/-- Expected real cost under the actual finite PMF. -/
def expectedCost (p : PMF A) (cost : A → ℝ) : ℝ :=
  ∑ a, (p a).toReal * cost a

/-- Finite real atom masses have total one. -/
theorem sum_probability_toReal (p : PMF A) : ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
  simpa only [tsum_fintype, ENNReal.toReal_one] using
    congrArg ENNReal.toReal p.tsum_coe

@[simp] theorem expectedCost_pure (a : A) (cost : A → ℝ) :
    expectedCost (PMF.pure a) cost = cost a := by
  simp [expectedCost, PMF.pure_apply, apply_ite]

/-- Real atom masses of a finite-domain bind are the literal weighted sum. -/
theorem bind_apply_toReal {C : Type*} (p : PMF A) (f : A → PMF C) (b : C) :
    ((p.bind f) b).toReal = ∑ a, (p a).toReal * (f a b).toReal := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum (fun a _ =>
    ENNReal.mul_ne_top (p.apply_ne_top a) ((f a).apply_ne_top b))]
  simp only [ENNReal.toReal_mul]

/-- The finite tower identity, with no sign assumptions on the cost. -/
theorem expectedCost_bind {C : Type*} [Fintype C] (p : PMF A) (f : A → PMF C)
    (cost : C → ℝ) :
    expectedCost (p.bind f) cost = ∑ a, (p a).toReal * expectedCost (f a) cost := by
  simp only [expectedCost, bind_apply_toReal, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact mul_assoc _ _ _

/-- Deterministic pushforward of finite expected cost. -/
theorem expectedCost_map {C : Type*} [Fintype C] (p : PMF A) (f : A → C)
    (cost : C → ℝ) :
    expectedCost (p.map f) cost = expectedCost p (fun a => cost (f a)) := by
  rw [PMF.map, expectedCost_bind]
  change (∑ a, (p a).toReal * expectedCost (PMF.pure (f a)) cost) =
    ∑ a, (p a).toReal * cost (f a)
  simp only [expectedCost_pure]

/-- Finite Markov's inequality, derived from a pointwise weighted inequality. -/
theorem threshold_mul_probability_le_expectedCost (p : PMF A) (cost : A → ℝ)
    (hcost : ∀ a, 0 ≤ cost a) (c : ℝ) (_hc : 0 ≤ c) :
    c * probability p (fun a => c < cost a) ≤ expectedCost p cost := by
  rw [probability_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases h : c < cost a
  · simp only [h, ite_true]
    nlinarith [ENNReal.toReal_nonneg (a := p a)]
  · simp only [h, ite_false, mul_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (hcost a)

/-- One draw exceeds twice a positive expected-cost bound with probability
at most one half. -/
theorem probability_cost_gt_twice_le_half (p : PMF A) (cost : A → ℝ)
    (hcost : ∀ a, 0 ≤ cost a) {B : ℝ} (hB : 0 < B)
    (hexpected : expectedCost p cost ≤ B) :
    probability p (fun a => 2 * B < cost a) ≤ (1 : ℝ) / 2 := by
  have h := threshold_mul_probability_le_expectedCost p cost hcost (2 * B) (by positivity)
  nlinarith

/-- The actual independent `T`-sample PMF. Normalization follows by expanding
the `T`th power of the sum of the atom masses. -/
def sampleLaw (p : PMF A) (T : ℕ) : PMF (Fin T → A) :=
  PMF.ofFintype (fun samples => ∏ i, p (samples i)) (by
    rw [← Fintype.sum_pow]
    have hp : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
    rw [hp, one_pow])

@[simp] theorem sampleLaw_apply (p : PMF A) (T : ℕ) (samples : Fin T → A) :
    sampleLaw p T samples = ∏ i, p (samples i) := rfl

/-- Every coordinate of a supported sample vector is a supported single draw. -/
theorem mem_support_sampleLaw_iff (p : PMF A) (T : ℕ) (samples : Fin T → A) :
    samples ∈ (sampleLaw p T).support ↔ ∀ i, samples i ∈ p.support := by
  simp [PMF.mem_support_iff, Finset.prod_ne_zero_iff]

/-- The full rectangle identity proves independence directly from the PMF. -/
theorem sampleLaw_rectangle (p : PMF A) (T : ℕ) (P : Fin T → A → Prop) :
    (sampleLaw p T).toOuterMeasure {samples | ∀ i, P i (samples i)} =
      ∏ i, p.toOuterMeasure {a | P i a} := by
  simp only [PMF.toOuterMeasure_apply_fintype, Set.indicator_apply,
    Set.mem_ofPred_eq, sampleLaw_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro samples _
  by_cases h : ∀ i, P i (samples i)
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [hi, ite_false]

/-- In particular, the probability that every draw fails is the `T`th power
of the single-draw failure probability, including the empty experiment. -/
theorem probability_all_samples (p : PMF A) (T : ℕ) (P : A → Prop) :
    probability (sampleLaw p T) (fun samples => ∀ i, P (samples i)) =
      probability p P ^ T := by
  unfold probability
  rw [sampleLaw_rectangle]
  simp

omit [Fintype A] in
theorem exists_minimum_index (cost : A → ℝ) {T : ℕ} (hT : 0 < T)
    (samples : Fin T → A) : ∃ i, ∀ j, cost (samples i) ≤ cost (samples j) := by
  let : Nonempty (Fin T) := ⟨⟨0, hT⟩⟩
  exact Finite.exists_min (fun i => cost (samples i))

/-- The chosen index witnesses that the output is a sample, even with ties. -/
def minimumIndex (cost : A → ℝ) {T : ℕ} (hT : 0 < T) (samples : Fin T → A) :
    Fin T := (exists_minimum_index cost hT samples).choose

/-- Return one actual sampled outcome having minimum sampled cost. -/
def selectMinimum (cost : A → ℝ) {T : ℕ} (hT : 0 < T) (samples : Fin T → A) : A :=
  samples (minimumIndex cost hT samples)

omit [Fintype A] in
theorem selectMinimum_is_sample (cost : A → ℝ) {T : ℕ} (hT : 0 < T)
    (samples : Fin T → A) : ∃ i, selectMinimum cost hT samples = samples i :=
  ⟨minimumIndex cost hT samples, rfl⟩

omit [Fintype A] in
theorem selectMinimum_cost_le (cost : A → ℝ) {T : ℕ} (hT : 0 < T)
    (samples : Fin T → A) (i : Fin T) :
    cost (selectMinimum cost hT samples) ≤ cost (samples i) :=
  (exists_minimum_index cost hT samples).choose_spec i

omit [Fintype A] in
theorem threshold_lt_selectMinimum_iff (cost : A → ℝ) {T : ℕ} (hT : 0 < T)
    (samples : Fin T → A) (c : ℝ) :
    c < cost (selectMinimum cost hT samples) ↔ ∀ i, c < cost (samples i) := by
  constructor
  · intro h i
    exact h.trans_le (selectMinimum_cost_le cost hT samples i)
  · intro h
    exact h (minimumIndex cost hT samples)

/-- Push the genuine independent sample law forward to its selected sample. -/
def outputLaw (p : PMF A) (cost : A → ℝ) {T : ℕ} (hT : 0 < T) : PMF A :=
  (sampleLaw p T).map (selectMinimum cost hT)

/-- Every supported output is an original supported outcome. -/
theorem support_outputLaw_subset (p : PMF A) (cost : A → ℝ) {T : ℕ} (hT : 0 < T) :
    (outputLaw p cost hT).support ⊆ p.support := by
  intro a ha
  obtain ⟨samples, hsamples, rfl⟩ :=
    (PMF.mem_support_map_iff (selectMinimum cost hT) (sampleLaw p T) a).mp ha
  exact (mem_support_sampleLaw_iff p T samples).mp hsamples (minimumIndex cost hT samples)

/-- Validity is preserved by selecting a minimum-cost sample. -/
theorem output_support_valid (p : PMF A) (cost : A → ℝ) {T : ℕ} (hT : 0 < T)
    (Valid : A → Prop) (hvalid : ∀ a ∈ p.support, Valid a) :
    ∀ a ∈ (outputLaw p cost hT).support, Valid a := by
  intro a ha
  exact hvalid a (support_outputLaw_subset p cost hT ha)

/-- The selected outcome fails exactly when all original independent draws fail. -/
theorem probability_output_gt (p : PMF A) (cost : A → ℝ) {T : ℕ} (hT : 0 < T)
    (c : ℝ) :
    probability (outputLaw p cost hT) (fun a => c < cost a) =
      probability p (fun a => c < cost a) ^ T := by
  change (((sampleLaw p T).map (selectMinimum cost hT)).toOuterMeasure
    {a | c < cost a}).toReal = _
  rw [PMF.toOuterMeasure_map_apply]
  have he : (selectMinimum cost hT) ⁻¹' {a | c < cost a} =
      {samples | ∀ i, c < cost (samples i)} := by
    ext samples
    exact threshold_lt_selectMinimum_iff cost hT samples c
  rw [he]
  exact probability_all_samples p T (fun a => c < cost a)

/-- Exponential amplification of the derived finite Markov estimate. -/
theorem probability_output_cost_gt_twice_le (p : PMF A) (cost : A → ℝ)
    (hcost : ∀ a, 0 ≤ cost a) {B : ℝ} (hB : 0 < B)
    (hexpected : expectedCost p cost ≤ B) {T : ℕ} (hT : 0 < T) :
    probability (outputLaw p cost hT) (fun a => 2 * B < cost a) ≤
      ((1 : ℝ) / 2) ^ T := by
  rw [probability_output_gt]
  exact pow_le_pow_left₀ (probability_nonneg p _) 
    (probability_cost_gt_twice_le_half p cost hcost hB hexpected) T

/-- The same exponential bound in the conventional `2⁻ᵀ` notation. -/
theorem probability_output_cost_gt_twice_le_two_rpow (p : PMF A) (cost : A → ℝ)
    (hcost : ∀ a, 0 ≤ cost a) {B : ℝ} (hB : 0 < B)
    (hexpected : expectedCost p cost ≤ B) {T : ℕ} (hT : 0 < T) :
    probability (outputLaw p cost hT) (fun a => 2 * B < cost a) ≤
      (2 : ℝ) ^ (-(T : ℝ)) := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  simpa only [one_div, inv_pow] using
    probability_output_cost_gt_twice_le p cost hcost hB hexpected hT

/-- An explicit positive number of trials for failure at most `n⁻κ`. -/
def sampleCount (n κ : ℝ) : ℕ := max 1 ⌈κ * Real.log n / Real.log 2⌉₊

theorem sampleCount_pos (n κ : ℝ) : 0 < sampleCount n κ := by
  exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem half_pow_sampleCount_le (n κ : ℝ) (hn : 1 ≤ n) (_hκ : 0 ≤ κ) :
    ((1 : ℝ) / 2) ^ sampleCount n κ ≤ n ^ (-κ) := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcount : κ * Real.log n / Real.log 2 ≤ (sampleCount n κ : ℝ) := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast (le_max_right 1 ⌈κ * Real.log n / Real.log 2⌉₊)
  have hmul := (div_le_iff₀ hl2).mp hcount
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    Real.rpow_def_of_pos hnpos]
  have hlog : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- The explicit sample count gives polynomially small failure. -/
theorem probability_output_cost_gt_twice_le_polynomial (p : PMF A) (cost : A → ℝ)
    (hcost : ∀ a, 0 ≤ cost a) {B : ℝ} (hB : 0 < B)
    (hexpected : expectedCost p cost ≤ B) (n κ : ℝ) (hn : 1 ≤ n) (hκ : 0 ≤ κ) :
    probability (outputLaw p cost (sampleCount_pos n κ)) (fun a => 2 * B < cost a) ≤
      n ^ (-κ) :=
  (probability_output_cost_gt_twice_le p cost hcost hB hexpected
    (sampleCount_pos n κ)).trans (half_pow_sampleCount_le n κ hn hκ)

/-- At expected cost zero, every supported outcome already has zero cost. -/
theorem cost_eq_zero_on_support (p : PMF A) (cost : A → ℝ)
    (hcost : ∀ a, 0 ≤ cost a) (hexpected : expectedCost p cost ≤ 0)
    {a : A} (ha : a ∈ p.support) : cost a = 0 := by
  have hterm : (p a).toReal * cost a ≤ expectedCost p cost :=
    Finset.single_le_sum (fun b _ => mul_nonneg ENNReal.toReal_nonneg (hcost b))
      (Finset.mem_univ a)
  have hp : 0 < (p a).toReal := ENNReal.toReal_pos ha (p.apply_ne_top a)
  nlinarith [hcost a]

/-- The zero-budget case preserves validity and has zero cost on the entire
output support, without dividing by the expected-cost bound. -/
theorem output_support_valid_zero_cost (p : PMF A) (cost : A → ℝ)
    (hcost : ∀ a, 0 ≤ cost a) (hexpected : expectedCost p cost ≤ 0)
    {T : ℕ} (hT : 0 < T) (Valid : A → Prop)
    (hvalid : ∀ a ∈ p.support, Valid a) :
    ∀ a ∈ (outputLaw p cost hT).support, Valid a ∧ cost a = 0 := by
  intro a ha
  have hp := support_outputLaw_subset p cost hT ha
  exact ⟨hvalid a hp, cost_eq_zero_on_support p cost hcost hexpected hp⟩

/-- In the zero-budget case the probability of strictly positive output cost
is zero for every positive sample count. -/
theorem probability_output_cost_positive_eq_zero (p : PMF A) (cost : A → ℝ)
    (hcost : ∀ a, 0 ≤ cost a) (hexpected : expectedCost p cost ≤ 0)
    {T : ℕ} (hT : 0 < T) :
    probability (outputLaw p cost hT) (fun a => 0 < cost a) = 0 := by
  have he : (outputLaw p cost hT).toOuterMeasure {a | 0 < cost a} = 0 := by
    apply (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
    apply Set.disjoint_left.mpr
    intro a ha hpos
    have hz := cost_eq_zero_on_support p cost hcost hexpected
      (support_outputLaw_subset p cost hT ha)
    exact (ne_of_gt hpos) hz
  simp only [probability, he, ENNReal.toReal_zero]

end

end DirectedFlowCutGap.FiniteAmplification
