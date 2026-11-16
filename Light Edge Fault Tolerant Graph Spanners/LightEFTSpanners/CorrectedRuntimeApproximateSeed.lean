import LightEFTSpanners.CorrectedRuntimeGuarantees
import LightEFTSpanners.CorrectedVotingApproximateSeed

/-! Supplied valid or two-approximate seeds transfer to the actual corrected
rational program. This certificate is an explicit assumption about the seed,
not a claimed implementation of the cited approximation algorithm. -/
namespace LightEFTSpanners.CorrectedRuntime
open SimpleGraph Finset FiniteProbability LightSpanners
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

theorem exists_seed_high_probability {G Q : SimpleGraph (Fin n)}
    (w : Sym2 (Fin n) → ℚ) (q f h k s : ℕ) (eps : ℚ)
    (hQ : IsFTConnectivityPreserver G Q q) (hbudget : 2*f+h≤q+1)
    (hf : 2≤f) (hh : 0<h) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ F : Fin (q+1) → SimpleGraph (Fin n),
      (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
      (CorrectedVoting.executionLaw (V:=Fin n) (J:=ForestComponentIndex F) f hf
        (CorrectedVoting.repetitionCount (Fintype.card (Fin n)) s) (input G Q (fun e => (w e:ℝ)))).prob (fun a => ¬(
          IsEFTSpanner G (output G Q w hw (paperStretch eps k)
            (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) h)
            (fun e => (w e:ℝ)) (paperStretch eps k:ℝ) f ∧
          totalWeight (output G Q w hw (paperStretch eps k)
            (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) h) (fun e => (w e:ℝ))≤
            (1+128*(f:ℝ)*extremalLightness n
              ((paperStretch eps k:ℝ)+1)/h)*totalWeight Q (fun e => (w e:ℝ)))) ≤ ((n:ℝ)^s)⁻¹ := by
  classical
  have hepsR : 0 < (eps:ℝ) := by exact_mod_cast heps
  have hwR : ∀ e, 0 ≤ (w e:ℝ) := by intro e; exact_mod_cast hw e
  have hwposR : ∀ e∈G.edgeSet, 0 < (w e:ℝ) := by
    intro e he; exact_mod_cast hwpos e he
  obtain ⟨F,hF,hprob⟩ := CorrectedVoting.exists_seed_high_probability
    (fun e => (w e:ℝ)) q f h k s (eps:ℝ) hQ hbudget hf hh hk hepsR hwR hwposR
  refine ⟨F,hF,?_⟩
  simpa only [output_eq,paperStretch_cast,Fintype.card_fin] using hprob

theorem exists_two_approximate_seed_high_probability (G Q : SimpleGraph (Fin n))
    (w : Sym2 (Fin n) → ℚ) (q f h k s : ℕ) (eps : ℚ)
    (hQ : IsFTConnectivityPreserver G Q q)
    (happrox : ∀ R,IsMinimumFTPreserver G R (fun e => (w e:ℝ)) q → totalWeight Q (fun e => (w e:ℝ))≤2*totalWeight R (fun e => (w e:ℝ)))
    (hbudget : 2*f+h≤q+1) (hf : 2≤f) (hh : 0<h) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ R : SimpleGraph (Fin n),IsMinimumFTPreserver G R (fun e => (w e:ℝ)) q ∧
      ∃ F : Fin (q+1) → SimpleGraph (Fin n),
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        (CorrectedVoting.executionLaw (V:=Fin n) (J:=ForestComponentIndex F) f hf
          (CorrectedVoting.repetitionCount (Fintype.card (Fin n)) s) (input G Q (fun e => (w e:ℝ)))).prob (fun a => ¬(
            IsEFTSpanner G (output G Q w hw (paperStretch eps k)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) h)
              (fun e => (w e:ℝ)) (paperStretch eps k:ℝ) f ∧
            competitiveLightness (output G Q w hw (paperStretch eps k)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) h) R (fun e => (w e:ℝ))≤
              2+256*(f:ℝ)*extremalLightness n
                ((paperStretch eps k:ℝ)+1)/h)) ≤ ((n:ℝ)^s)⁻¹ := by
  classical
  have hepsR : 0 < (eps:ℝ) := by exact_mod_cast heps
  have hwR : ∀ e, 0 ≤ (w e:ℝ) := by intro e; exact_mod_cast hw e
  have hwposR : ∀ e∈G.edgeSet, 0 < (w e:ℝ) := by
    intro e he; exact_mod_cast hwpos e he
  obtain ⟨R,hR,F,hF,hprob⟩ := CorrectedVoting.exists_two_approximate_seed_high_probability
    G Q (fun e => (w e:ℝ)) q f h k s (eps:ℝ) hQ happrox hbudget hf hh hk hepsR hwR hwposR
  refine ⟨R,hR,F,hF,?_⟩
  simpa only [output_eq,paperStretch_cast,Fintype.card_fin] using hprob

end LightEFTSpanners.CorrectedRuntime
