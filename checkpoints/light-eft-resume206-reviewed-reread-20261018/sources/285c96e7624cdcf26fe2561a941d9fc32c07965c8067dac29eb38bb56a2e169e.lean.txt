import LightEFTSpanners.ProductSampleConcentration

namespace LightEFTSpanners.FiniteProbability
open Finset MeasureTheory
variable {α J : Type*} [Fintype α] [Fintype J] [DecidableEq J]

noncomputable def productLaw (p : Law α) : Law (J → α) where
  mass x := ∏ i,p.mass (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => p.nonneg (x i))
  total := by rw [←Fintype.prod_sum];simp only [p.total,Finset.prod_const_one]

theorem productLaw_measure [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : Law α) : productLaw (J:=J) p=Law.ofMeasure (Measure.pi (fun _ : J => p.toPMF.toMeasure)) := by
  unfold productLaw Law.ofMeasure
  congr 1
  funext x
  rw [Measure.real,Measure.pi_singleton,ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [p.toPMF.toMeasure_apply_singleton _ (measurableSet_singleton _)]
  simp only [Law.toPMF,PMF.ofFintype_apply,ENNReal.toReal_ofReal (p.nonneg _)]
end LightEFTSpanners.FiniteProbability
