import LightEFTSpanners.FiniteProductLaw
import LightEFTSpanners.StoredFlagBatchExecutable
import LightEFTSpanners.StoredFlagSampleProbability

namespace LightEFTSpanners.StoredFlagBatch
open Finset FiniteProbability MeasureTheory
attribute [local instance] Classical.propDecidable
local instance (n : ℕ) : MeasurableSpace (Finset (Sym2 (Fin n))) := ⊤

noncomputable def sourceLaw (n f m : ℕ) (hf : 0<f) : Law (Fin m → Sym2 (Fin n) → Bool) :=
  productLaw (StoredFlagSample.sourceLaw n f hf)

theorem original_probability (n f m : ℕ) (hf : 0<f)
    (P : (Fin m → Finset (Sym2 (Fin n))) → Prop) :
    (sourceLaw n f m hf).prob (fun bits => P (fun i => BernoulliFlags.selected (bits i)))=
      (drawLaw (SampledGreedy.bernoulliLaw (V:=Fin n) f hf).toPMF.toMeasure m).prob P := by
  have he := Equiv.sum_comp
    (Equiv.piCongrRight (fun _ : Fin m => BernoulliFlags.flagEquiv (α:=Sym2 (Fin n))))
    (fun S => if P S then ∏ i,(SampledGreedy.bernoulliLaw (V:=Fin n) f hf).mass (S i) else 0)
  have h : (sourceLaw n f m hf).prob (fun bits => P (fun i => BernoulliFlags.selected (bits i)))=
      (productLaw (J:=Fin m) (SampledGreedy.bernoulliLaw (V:=Fin n) f hf)).prob P := by
    unfold Law.prob sourceLaw productLaw StoredFlagSample.sourceLaw BernoulliFlags.law
    simp_rw [BernoulliFlags.productMass_eq]
    exact he
  rw [h,productLaw_measure]
  rfl

def OutputSatisfies (n m : ℕ) (P : (Fin m → Finset (Sym2 (Fin n))) → Prop) (es : Output) : Prop :=
  ∃ typed : Fin m → List (Fin n × Fin n),
    List.ofFn (fun i => StoredEdges.encode (typed i))=es ∧ P (fun i => StoredSample.edgeSet (typed i))

theorem actual_failure_le (n f m : ℕ) (hf : 0<f)
    (P : (Fin m → Finset (Sym2 (Fin n))) → Prop) :
    (sourceLaw n f m hf).prob (fun bits => ¬OutputSatisfies n m P
      (execute (List.ofFn (fun i => StoredFlagSample.entries (bits i)))))≤
      (drawLaw (SampledGreedy.bernoulliLaw (V:=Fin n) f hf).toPMF.toMeasure m).prob (fun x => ¬P x) := by
  rw [←original_probability n f m hf (fun x => ¬P x)]
  apply Law.prob_mono
  intro bits bad good
  apply bad
  refine ⟨fun i => StoredFlagSample.typed (bits i),?_,?_⟩
  · have he := execute_encoded (List.ofFn bits)
    simpa only [List.map_ofFn,Function.comp_def] using he.symm
  · simpa only [StoredFlagSample.typed_edgeSet] using good
end LightEFTSpanners.StoredFlagBatch
