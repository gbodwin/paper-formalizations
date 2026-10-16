import LightEFTSpanners.FiniteLaw

namespace LightEFTSpanners.FiniteProbability.Law
open Finset
variable {α β : Type*} [Fintype α] [Fintype β]
attribute [local instance] Classical.propDecidable

 theorem prob_const (p : Law α) (P : Prop) : p.prob (fun _ => P) = if P then 1 else 0 := by
  by_cases h : P <;> simp [prob,h,p.total]

 theorem prob_not (p : Law α) (P : α → Prop) : p.prob (fun a => ¬P a)=1-p.prob P := by
  have h : p.prob (fun a => ¬P a)+p.prob P=1 := by
    rw [prob,prob,←sum_add_distrib,←p.total]
    apply sum_congr rfl
    intro a _
    by_cases ha : P a <;> simp [ha]
  linarith

/-- Adaptive finite union bound: the next batch is drawn only after fixing
the old random outcome. Only the actually reached state is tested. -/
theorem fresh_step_failure (p : Law α) (q : Law β) (update : α → β → α)
    (oldGood newGood : α → Prop) (bad : α → β → Prop) (δ : ℝ)
    (hnew : ∀ a b, ¬newGood (update a b) → ¬oldGood a ∨ bad a b)
    (hbad : ∀ a, q.prob (bad a)≤δ) :
    (p.bind (fun a => q.map (update a))).prob (fun a => ¬newGood a) ≤
      p.prob (fun a => ¬oldGood a)+δ := by
  rw [prob_bind]
  calc
    _ ≤ ∑ a,p.mass a*((if ¬oldGood a then 1 else 0)+δ) := by
      apply sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (p.nonneg a)
      rw [prob_map]
      calc
        _ ≤ q.prob (fun b => ¬oldGood a ∨ bad a b) := q.prob_mono (fun b => hnew a b)
        _ ≤ q.prob (fun _ => ¬oldGood a)+q.prob (bad a) := q.prob_or_le _ _
        _ ≤ _ := by
          rw [prob_const]
          by_cases ho : oldGood a <;> simpa [ho] using hbad a
    _ = _ := by
      simp_rw [mul_add,mul_ite,mul_one,mul_zero]
      rw [sum_add_distrib,←sum_mul,p.total,one_mul]
      congr 1
      unfold prob
      apply sum_congr rfl
      intro a _
      by_cases ho : oldGood a <;> simp [ho]
end LightEFTSpanners.FiniteProbability.Law
