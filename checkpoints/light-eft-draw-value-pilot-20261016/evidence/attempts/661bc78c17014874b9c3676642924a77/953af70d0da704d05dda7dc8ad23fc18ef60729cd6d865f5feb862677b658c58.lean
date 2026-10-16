import LightEFTSpanners.ProductSampleConcentration
import LightEFTSpanners.EmpiricalVotingGreedy
import LightEFTSpanners.SamplingRestriction

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners LightSpanners.FiniteSampling
open MeasureTheory FiniteProbability
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Draw all original identities independently, then the test clips the sample
to the actual reached non-seed edges. This fixed finite law is fresh at every call. -/
noncomputable def bernoulliLaw (f : ℕ) (hf : 0<f) : Law (Finset (Sym2 V)) where
  mass S := mass univ (1/(2*(f:ℝ))) S
  nonneg S := by
    have hf1 : (1:ℝ)≤f := by exact_mod_cast hf
    exact mass_nonneg _ _ (by positivity) ((div_le_one (by positivity)).mpr (by linarith))
  total := by
    have hu : (univ : Finset (Sym2 V)).powerset=univ := by ext S;simp
    simpa only [hu] using sum_mass (univ : Finset (Sym2 V)) (1/(2*(f:ℝ)))

local instance : MeasurableSpace (Finset (Sym2 V)) := ⊤

 theorem integral_test_indicator (Q E T : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t : ℝ) (f : ℕ) (hf : 0<f) (e : Sym2 V) :
    (∫ S, (if ¬Covered (testSample Q E T S) w t e then (1:ℝ) else 0)
      ∂(bernoulliLaw (V:=V) f hf).toPMF.toMeasure) = testProbability Q E T w t f e := by
  rw [Law.integral_toPMF]
  have hu : (univ : Finset (Sym2 V)).powerset=univ := by ext S;simp
  have hr := sum_mass_restrict (univ : Finset (Sym2 V)) (E\Q) (1/(2*(f:ℝ)))
    (fun S => if ¬Covered (edgeGraph (T∪S)) w t e then (1:ℝ) else 0) (subset_univ _)
  rw [hu] at hr
  change (∑ S, mass univ (1/(2*(f:ℝ))) S *
    (if ¬Covered (edgeGraph (T∪(S∩(E\Q)))) w t e then (1:ℝ) else 0)) = _
  rw [hr]
  unfold testProbability
  rw [sum_filter]
  apply sum_congr rfl
  intro S hS
  have hh : S∩(E\Q)=S := inter_eq_left.mpr (mem_powerset.mp hS)
  simp only [testSample,hh]
  split_ifs <;> ring

private theorem filter_length_indicator {α : Type*} (b : α → Bool) (l : List α) :
    ((l.filter b).length:ℝ) = (l.map (fun a => if b a then (1:ℝ) else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => cases h : b a <;> simp [h,ih,Nat.cast_add,add_comm]

omit [Fintype V] in
 theorem estimate_ofFn (Q E T : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t : ℝ) (e : Sym2 V) (m : ℕ) (x : Fin m → Finset (Sym2 V)) :
    estimate Q E T w t e (List.ofFn x) =
      (∑ i, if ¬Covered (testSample Q E T (x i)) w t e then (1:ℝ) else 0)/(m:ℝ) := by
  unfold estimate
  rw [filter_length_indicator]
  simp [List.map_ofFn,List.sum_ofFn]

noncomputable def testDrawMeasure (f : ℕ) (hf : 0<f) (m : ℕ) :
    Measure (Fin m → Finset (Sym2 V)) := drawMeasure (bernoulliLaw (V:=V) f hf).toPMF.toMeasure m

instance testDrawMeasure_probability (f : ℕ) (hf : 0<f) (m : ℕ) :
    IsProbabilityMeasure (testDrawMeasure (V:=V) f hf m) := by
  unfold testDrawMeasure
  infer_instance

 theorem test_estimate_tail (Q E T : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t : ℝ) (f : ℕ) (hf : 0<f) (e : Sym2 V) (m : ℕ) (hm : 0<m) :
    (testDrawMeasure (V:=V) f hf m).real {x | 1/8 <
      |estimate Q E T w t e (List.ofFn x)-testProbability Q E T w t f e|} ≤
      2*Real.exp (-(m:ℝ)/32) := by
  have h := indicator_sample_tail (bernoulliLaw (V:=V) f hf).toPMF.toMeasure
    (fun S => ¬Covered (testSample Q E T S) w t e) m hm
  rw [drawLaw, Law.prob_ofMeasure] at h
  have hp : (bernoulliLaw (V:=V) f hf).toPMF.toMeasure.real
      {S | ¬Covered (testSample Q E T S) w t e} = testProbability Q E T w t f e := by
    rw [← integral_indicator_one (Set.toFinite {S | ¬Covered (testSample Q E T S) w t e}).measurableSet]
    calc
      _ = ∫ S, (if ¬Covered (testSample Q E T S) w t e then (1:ℝ) else 0)
          ∂(bernoulliLaw (V:=V) f hf).toPMF.toMeasure := by
        apply integral_congr_ae
        filter_upwards [] with S
        by_cases hc : Covered (testSample Q E T S) w t e <;> simp [Set.indicator,hc]
      _ = _ := integral_test_indicator Q E T w t f hf e
  rw [hp] at h
  change _ ≤ _ at h
  convert h using 1
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [estimate_ofFn]
  simp only [ite_not]
  have hs : (∑ i, if Covered (testSample Q E T (x i)) w t e then (0:ℝ) else 1) =
      (∑ i, @ite ℝ (¬Covered (testSample Q E T (x i)) w t e)
        (Classical.propDecidable _) 1 0) := by
    apply sum_congr rfl
    intro i _
    by_cases hc : Covered (testSample Q E T (x i)) w t e <;> simp [hc]
  exact Iff.of_eq (congrArg (fun z : ℝ => 1/8 < |z/(m:ℝ)-testProbability Q E T w t f e|) hs)

/-- Every host receives its own independent m-draw batch. -/
noncomputable def freshBatchLaw {J : Type*} [Fintype J] [DecidableEq J] (f : ℕ) (hf : 0<f) (m : ℕ) :
    Law (J → Fin m → Finset (Sym2 V)) := batchLaw (testDrawMeasure (V:=V) f hf m)

 theorem fresh_batch_bad_le {J : Type*} [Fintype J] [DecidableEq J]
    (Q E : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ) (hf : 0<f)
    (e : Sym2 V) (m : ℕ) (hm : 0<m) (s : Finset J) (host : J → Finset (Sym2 V)) :
    (freshBatchLaw (V:=V) (J:=J) f hf m).prob (fun x => ∃ j∈s, 1/8 <
      |estimate Q E (host j) w t e (List.ofFn (x j))-testProbability Q E (host j) w t f e|) ≤
      s.card*(2*Real.exp (-(m:ℝ)/32)) :=
  batchLaw_bad_le _ s _ _ (fun j _ => test_estimate_tail Q E (host j) w t f hf e m hm)
end LightEFTSpanners.SampledGreedy
