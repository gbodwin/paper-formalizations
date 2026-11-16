import LightEFTSpanners.CorrectedRuntimeOutput
import LightEFTSpanners.CorrectedVotingGuarantees

/-! The high-probability guarantees apply to the actual rational output with
acceptance threshold 1/8. Seed and packing preparation are mathematical choices;
their efficient construction and random generation are not runtime premises
silently discharged by these theorems. The conditional supplied-input loop
bound is proved separately in CorrectedRuntimeWork. -/
namespace LightEFTSpanners.CorrectedRuntime
open SimpleGraph Finset FiniteProbability LightSpanners
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

/-- The actual corrected rational recursion is both fault tolerant and light
under the independently sampled 1/f assignment law, with failure probability
at most n^(-s). This is a program-output theorem, not a seed-preparation cost claim. -/
theorem exists_algorithm_two_high_probability (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℚ)
    (f k s : ℕ) (eps : ℚ) (hf : 2≤f) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ Q : SimpleGraph (Fin n),IsMinimumFTPreserver G Q (fun e => (w e:ℝ)) (2*f) ∧
      ∃ F : Fin (2*f+1) → SimpleGraph (Fin n),
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        (CorrectedVoting.executionLaw (V:=Fin n) (J:=ForestComponentIndex F) f hf
          (CorrectedVoting.repetitionCount (Fintype.card (Fin n)) s) (input G Q (fun e => (w e:ℝ)))).prob (fun a => ¬(
            IsEFTSpanner G (output G Q w hw (paperStretch eps k)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) 1) (fun e => (w e:ℝ)) (paperStretch eps k:ℝ) f ∧
            competitiveLightness (output G Q w hw (paperStretch eps k)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) 1) Q (fun e => (w e:ℝ))≤
              1+128*(f:ℝ)*extremalLightness n ((paperStretch eps k:ℝ)+1))) ≤
          ((n:ℝ)^s)⁻¹ := by
  classical
  have hepsR : 0 < (eps:ℝ) := by exact_mod_cast heps
  have hwR : ∀ e, 0 ≤ (w e:ℝ) := by intro e; exact_mod_cast hw e
  have hwposR : ∀ e∈G.edgeSet, 0 < (w e:ℝ) := by
    intro e he; exact_mod_cast hwpos e he
  obtain ⟨Q,hQ,F,hF,hprob⟩ := CorrectedVoting.exists_algorithm_two_high_probability
    G (fun e => (w e:ℝ)) f k s (eps:ℝ) hf hk hepsR hwR hwposR
  refine ⟨Q,hQ,F,hF,?_⟩
  simpa only [output_eq,paperStretch_cast,Fintype.card_fin] using hprob

/-- The actual corrected rational recursion is both fault tolerant and light
under the independently sampled 1/f assignment law, with failure probability
at most n^(-s). This is a program-output theorem, not a seed-preparation cost claim. -/
theorem exists_algorithm_three_high_probability (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℚ)
    (f k s : ℕ) (eps : ℚ) (eta : ℝ) (hf : 2≤f) (hk : 0<k) (heps : 0<eps) (heta : 0<eta)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ Q : SimpleGraph (Fin n),IsMinimumFTPreserver G Q (fun e => (w e:ℝ)) ⌊(2+eta)*(f:ℝ)⌋₊ ∧
      ∃ F : Fin (⌊(2+eta)*(f:ℝ)⌋₊+1) → SimpleGraph (Fin n),
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        (CorrectedVoting.executionLaw (V:=Fin n) (J:=ForestComponentIndex F) f hf
          (CorrectedVoting.repetitionCount (Fintype.card (Fin n)) s) (input G Q (fun e => (w e:ℝ)))).prob (fun a => ¬(
            IsEFTSpanner G (output G Q w hw (paperStretch eps k)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) (⌊eta*(f:ℝ)⌋₊+1))
              (fun e => (w e:ℝ)) (paperStretch eps k:ℝ) f ∧
            competitiveLightness (output G Q w hw (paperStretch eps k)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) (⌊eta*(f:ℝ)⌋₊+1)) Q (fun e => (w e:ℝ))≤
              1+128*extremalLightness n ((paperStretch eps k:ℝ)+1)/eta)) ≤
          ((n:ℝ)^s)⁻¹ := by
  classical
  have hepsR : 0 < (eps:ℝ) := by exact_mod_cast heps
  have hwR : ∀ e, 0 ≤ (w e:ℝ) := by intro e; exact_mod_cast hw e
  have hwposR : ∀ e∈G.edgeSet, 0 < (w e:ℝ) := by
    intro e he; exact_mod_cast hwpos e he
  obtain ⟨Q,hQ,F,hF,hprob⟩ := CorrectedVoting.exists_algorithm_three_high_probability
    G (fun e => (w e:ℝ)) f k s (eps:ℝ) eta hf hk hepsR heta hwR hwposR
  refine ⟨Q,hQ,F,hF,?_⟩
  simpa only [output_eq,paperStretch_cast,Fintype.card_fin] using hprob

end LightEFTSpanners.CorrectedRuntime
