import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Unconditional bounds for a history-dependent weighted sampler

The construction history may contain rational rows, arbitrary bit strings and
retained events. No finite-type instance is imposed on that history or on the
sampler output. A bound valid on good construction histories, plus the actual
probability of bad histories, bounds the unconditional output event.

This is the probability-composition lemma only. The actual controller must
still establish its good-history event and error probability, and the concrete
weighted sampler must establish its conditional bound. No independence between
the construction history and its continuation is assumed.
-/
namespace DirectedFlowCutGap.WeightedMixtureBound

open scoped ENNReal

noncomputable section

variable {A B : Type*}

theorem event_le_one (p : PMF A) (s : Set A) : p.toOuterMeasure s ≤ 1 := by
  have h : p.toOuterMeasure s ≤ p.toOuterMeasure Set.univ :=
    p.toOuterMeasure_mono (Set.subset_univ _)
  exact h.trans_eq ((PMF.toOuterMeasure_apply_eq_one_iff p Set.univ).mpr
    (Set.subset_univ _))

/-- Only histories in the actual construction support need a conditional
bound. An arbitrary cost-bad history contributes at most its own probability. -/
theorem bind_event_le (p : PMF A) (next : A → PMF B) (good : A → Prop)
    (event : Set B) (bound : ℝ≥0∞)
    (hgood : ∀ a ∈ p.support, good a → (next a).toOuterMeasure event ≤ bound) :
    (p.bind next).toOuterMeasure event ≤
      bound + p.toOuterMeasure {a | ¬ good a} := by
  classical
  have step (a : A) :
      p a * (next a).toOuterMeasure event ≤
        p a * bound + (if good a then 0 else p a) := by
    by_cases hp : p a = 0
    · simp [hp]
    · have hs : a ∈ p.support := by simpa only [PMF.mem_support_iff] using hp
      by_cases hg : good a
      · simpa [hg] using mul_le_mul' (le_refl (p a)) (hgood a hs hg)
      · have he := mul_le_mul' (le_refl (p a)) (event_le_one (next a) event)
        simp only [mul_one] at he
        simpa [hg] using he.trans (le_add_self : p a ≤ p a * bound + p a)
  rw [PMF.toOuterMeasure_bind_apply]
  calc
    (∑' a, p a * (next a).toOuterMeasure event) ≤
        ∑' a, (p a * bound + (if good a then 0 else p a)) :=
      ENNReal.tsum_le_tsum step
    _ = bound + p.toOuterMeasure {a | ¬ good a} := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
        PMF.toOuterMeasure_apply]
      congr 1
      apply tsum_congr
      intro a
      by_cases hg : good a <;> simp [hg]

/-- Oracle and sampling errors stay separate until their independently proved
bounds are combined. This statement is unconditional over all histories. -/
theorem bind_event_le_errors (p : PMF A) (next : A → PMF B) (good : A → Prop)
    (event : Set B) (mainBound oracleError samplerError : ℝ≥0∞)
    (hgood : ∀ a ∈ p.support, good a →
      (next a).toOuterMeasure event ≤ mainBound + samplerError)
    (hbad : p.toOuterMeasure {a | ¬ good a} ≤ oracleError) :
    (p.bind next).toOuterMeasure event ≤ mainBound + samplerError + oracleError :=
  (bind_event_le p next good event _ hgood).trans (add_le_add le_rfl hbad)

/-- Exact support avoidance survives every continuation, including failure
and fallback histories. It is stronger than any positive error tolerance. -/
theorem bind_event_zero (p : PMF A) (next : A → PMF B) (event : Set B)
    (hzero : ∀ a ∈ p.support, (next a).toOuterMeasure event = 0) :
    (p.bind next).toOuterMeasure event = 0 := by
  classical
  rw [PMF.toOuterMeasure_bind_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro a
  by_cases hp : p a = 0
  · simp [hp]
  · have hs : a ∈ p.support := by simpa only [PMF.mem_support_iff] using hp
    rw [hzero a hs, mul_zero]

end

end DirectedFlowCutGap.WeightedMixtureBound
