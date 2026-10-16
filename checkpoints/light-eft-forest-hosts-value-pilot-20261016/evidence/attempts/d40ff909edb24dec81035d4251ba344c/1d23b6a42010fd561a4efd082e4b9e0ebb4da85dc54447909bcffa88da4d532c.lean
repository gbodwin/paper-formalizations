import LightEFTSpanners.FiniteHoeffding
import LightEFTSpanners.FiniteLaw

namespace LightEFTSpanners.FiniteProbability
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
attribute [local instance] Classical.propDecidable

/-- The literal product measure of m fresh independent draws. -/
noncomputable def drawMeasure (μ : Measure α) (m : ℕ) : Measure (Fin m → α) :=
  Measure.pi (fun _ => μ)

instance drawMeasure_probability (μ : Measure α) [IsProbabilityMeasure μ] (m : ℕ) :
    IsProbabilityMeasure (drawMeasure μ m) := by unfold drawMeasure; infer_instance

/-- A finite draw law is constructed from the product measure, with no
statistical accuracy assumption. -/
noncomputable def drawLaw (μ : Measure α) [IsProbabilityMeasure μ] (m : ℕ) : Law (Fin m → α) :=
  Law.ofMeasure (drawMeasure μ m)

 theorem indicator_sample_tail (μ : Measure α) [IsProbabilityMeasure μ]
    (P : α → Prop) (m : ℕ) (hm : 0<m) :
    (drawLaw μ m).prob (fun x => 1/8 <
      |(∑ i, if P (x i) then (1:ℝ) else 0)/(m:ℝ) - μ.real {a | P a}|) ≤
      2*Real.exp (-(m:ℝ)/32) := by
  let b : α → ℝ := fun a => if P a then 1 else 0
  have hb : Measurable b := measurable_of_finite b
  have hint : (∫ a, b a ∂μ) = μ.real {a | P a} := by
    simpa [b, Set.indicator] using
      (integral_indicator_one (μ:=μ) (Set.toFinite {a | P a}).measurableSet)
  have he (i : Fin m) : (∫ x, b (x i) ∂drawMeasure μ m) = μ.real {a | P a} := by
    rw [←hint]
    calc
      _ = ∫ a, b a ∂(Measure.pi (fun _ : Fin m => μ)).map (Function.eval i) :=
        (integral_map (measurable_pi_apply i).aemeasurable hb.aestronglyMeasurable).symm
      _ = _ := by rw [(measurePreserving_eval (fun _ : Fin m => μ) i).map_eq]
  have hi : iIndepFun (fun i : Fin m => fun x : Fin m → α => b (x i)) (drawMeasure μ m) :=
    iIndepFun_pi (fun _ => hb.aemeasurable)
  have h := bounded_mean_tail (drawMeasure μ m) m hm (fun i x => b (x i))
    (fun i => (hb.comp (measurable_pi_apply i)).aemeasurable) hi
    (fun i => ae_of_all _ fun x => by dsimp [b]; split_ifs <;> norm_num)
  rw [drawLaw, Law.prob_ofMeasure]
  have heq (x : Fin m → α) :
      (∑ i, (b (x i) - ∫ y, b (y i) ∂drawMeasure μ m))/(m:ℝ) =
        (∑ i, if P (x i) then (1:ℝ) else 0)/(m:ℝ) - μ.real {a | P a} := by
    simp only [he, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hm0 : (m:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hm
    dsimp [b]
    rw [sub_div, mul_div_cancel_left₀ _ hm0]
  simpa only [heq] using h
end LightEFTSpanners.FiniteProbability

namespace LightEFTSpanners.FiniteProbability
open MeasureTheory Finset
variable {α J : Type*} [Fintype α] [Fintype J] [DecidableEq J]
    [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Independent whole batches, one for every host; unused hosts do not matter. -/
noncomputable def batchLaw (μ : Measure α) [IsProbabilityMeasure μ] : Law (J → α) :=
  Law.ofMeasure (Measure.pi (fun _ : J => μ))

 theorem batchLaw_eval (μ : Measure α) [IsProbabilityMeasure μ] (j : J) (P : α → Prop) :
    (batchLaw (J:=J) μ).prob (fun x => P (x j)) = μ.real {a | P a} := by
  rw [batchLaw, Law.prob_ofMeasure]
  have h := (measurePreserving_eval (fun _ : J => μ) j).measure_preimage
    (Set.toFinite {a | P a}).measurableSet.nullMeasurableSet
  exact congrArg ENNReal.toReal h

 theorem batchLaw_bad_le (μ : Measure α) [IsProbabilityMeasure μ]
    (s : Finset J) (P : J → α → Prop) (δ : ℝ)
    (h : ∀ j∈s, μ.real {a | P j a}≤δ) :
    (batchLaw (J:=J) μ).prob (fun x => ∃ j∈s, P j (x j)) ≤ s.card*δ := by
  calc
    _ ≤ ∑ j∈s, (batchLaw (J:=J) μ).prob (fun x => P j (x j)) :=
      Law.prob_exists_le _ s _
    _ ≤ ∑ _j∈s, δ := sum_le_sum (fun j hj => by rw [batchLaw_eval];exact h j hj)
    _ = _ := by simp
end LightEFTSpanners.FiniteProbability
