import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace LightEFTSpanners.FiniteProbability
open Finset MeasureTheory
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- A literal normalized finite real probability mass. -/
structure Law (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace Law
attribute [local instance] Classical.propDecidable
noncomputable def prob (p : Law α) (P : α → Prop) : ℝ :=
  ∑ a, if P a then p.mass a else 0

theorem prob_nonneg (p : Law α) (P : α → Prop) : 0 ≤ p.prob P := by
  apply sum_nonneg
  intro a _
  split_ifs <;> simp [p.nonneg]

@[simp] theorem prob_true (p : Law α) : p.prob (fun _ => True) = 1 := by
  simpa [prob] using p.total

noncomputable def pure (a : α) : Law α where
  mass b := if b=a then 1 else 0
  nonneg b := by split_ifs <;> norm_num
  total := by
    classical
    simp

/-- Each call samples afresh from q after the old outcome has been fixed. -/
noncomputable def bind (p : Law α) (q : α → Law β) : Law β where
  mass b := ∑ a, p.mass a * (q a).mass b
  nonneg b := sum_nonneg (fun a _ => mul_nonneg (p.nonneg a) ((q a).nonneg b))
  total := by
    rw [sum_comm]
    simp_rw [← mul_sum, (q _).total, mul_one]
    exact p.total

noncomputable def map (p : Law α) (g : α → β) : Law β := p.bind (fun a => pure (g a))

theorem prob_bind (p : Law α) (q : α → Law β) (P : β → Prop) :
    (p.bind q).prob P = ∑ a, p.mass a * (q a).prob P := by
  unfold prob
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  by_cases hb : P b <;> simp [hb, bind]

@[simp] theorem prob_pure (a : α) (P : α → Prop) :
    (pure a).prob P = if P a then 1 else 0 := by
  classical
  unfold prob
  rw [sum_eq_single a]
  · simp [pure]
  · intro b _ hb
    simp [pure, hb]
  · simp

theorem prob_map (p : Law α) (g : α → β) (P : β → Prop) :
    (p.map g).prob P = p.prob (fun a => P (g a)) := by
  rw [map, prob_bind]
  simp_rw [prob_pure]
  simp [prob, mul_ite]

theorem prob_mono (p : Law α) {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    p.prob P ≤ p.prob Q := by
  apply sum_le_sum
  intro a _
  by_cases hp : P a <;> by_cases hq : Q a <;> simp_all [p.nonneg]

theorem prob_or_le (p : Law α) (P Q : α → Prop) :
    p.prob (fun a => P a ∨ Q a) ≤ p.prob P + p.prob Q := by
  rw [prob, prob, prob, ← sum_add_distrib]
  apply sum_le_sum
  intro a _
  by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp,hq,p.nonneg]

theorem prob_exists_le (p : Law α) {ι : Type*} (s : Finset ι) (P : ι → α → Prop) :
    p.prob (fun a => ∃ i∈s, P i a) ≤ ∑ i∈s, p.prob (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [prob]
  | @insert i s hi ih =>
    have h : p.prob (fun a => ∃ j∈insert i s, P j a) =
        p.prob (fun a => P i a ∨ ∃ j∈s, P j a) := by
      congr 1
      funext a
      simp
    rw [h, sum_insert hi]
    exact (p.prob_or_le _ _).trans (add_le_add le_rfl ih)

noncomputable def toPMF (p : Law α) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (p.mass a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => p.nonneg a), p.total]
    simp)

 theorem integral_toPMF [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : Law α) (g : α → ℝ) :
    (∫ a, g a ∂p.toPMF.toMeasure) = ∑ a, p.mass a*g a := by
  rw [PMF.integral_eq_sum]
  simp only [toPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (p.nonneg _), smul_eq_mul]

/-- Finite probability measures supply exactly their real singleton masses. -/
noncomputable def ofMeasure [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] : Law α where
  mass a := μ.real {a}
  nonneg _ := measureReal_nonneg
  total := by simp

theorem prob_ofMeasure [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] (P : α → Prop) :
    (ofMeasure μ).prob P = μ.real {a | P a} := by
  rw [← integral_indicator_one (Set.toFinite {a | P a}).measurableSet, integral_fintype (Integrable.of_finite)]
  unfold prob
  apply sum_congr rfl
  intro a _
  by_cases h : P a <;> simp [ofMeasure, Set.indicator, h]
end Law
end LightEFTSpanners.FiniteProbability
