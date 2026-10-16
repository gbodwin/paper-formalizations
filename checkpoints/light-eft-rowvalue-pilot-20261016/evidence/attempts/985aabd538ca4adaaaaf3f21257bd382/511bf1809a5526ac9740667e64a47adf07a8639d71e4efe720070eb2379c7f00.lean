import LightEFTSpanners.StoredFlagSampleEncoding
import LightEFTSpanners.StoredOutputLaw

namespace LightEFTSpanners.StoredFlagSample
open Finset FiniteProbability
attribute [local instance] Classical.propDecidable

noncomputable def sourceLaw (n f : ℕ) (hf : 0<f) : Law (Sym2 (Fin n) → Bool) :=
  BernoulliFlags.law (1/(2*(f:ℝ))) (by positivity) (by
    have hf1 : (1:ℝ)≤f := by exact_mod_cast hf
    apply (div_le_one (by positivity)).mpr
    linarith)

theorem original_probability (n f : ℕ) (hf : 0<f) (P : Finset (Sym2 (Fin n)) → Prop) :
    (sourceLaw n f hf).prob (fun bits => P (StoredSample.edgeSet (typed bits)))=
      (SampledGreedy.bernoulliLaw (V:=Fin n) f hf).prob P := by
  simp only [typed_edgeSet]
  rw [sourceLaw,BernoulliFlags.probability_selected]
  rfl

theorem actual_failure_le (n f : ℕ) (hf : 0<f) (P : Finset (Sym2 (Fin n)) → Prop) :
    (sourceLaw n f hf).prob (fun bits => ¬StoredCandidates.OutputSatisfies n P (execute (entries bits)))≤
      (SampledGreedy.bernoulliLaw (V:=Fin n) f hf).prob (fun S => ¬P S) := by
  rw [←original_probability n f hf (fun S => ¬P S)]
  apply Law.prob_mono
  intro bits bad good
  exact bad ⟨typed bits,execute_encoded bits,good⟩
end LightEFTSpanners.StoredFlagSample
