import LightEFTSpanners.CorrectedRuntimeOutput
import LightEFTSpanners.CorrectedVotingConstructedWeight
import LightEFTSpanners.CorrectedVotingPolynomialSamples

/-! The same supplied-input rational program has both a paid loop bound and
a high-probability correctness/lightness guarantee. The repetition count is
the computable polynomial 128(s+5)n+1. A valid two-approximate seed and its
efficient preparation remain explicit input obligations. The cost conclusion
uses the abstract finite-set/table-access loop metric of CorrectedRuntimeWork;
it is not an end-to-end concrete machine running-time theorem. -/
namespace LightEFTSpanners.CorrectedRuntime
open SimpleGraph Finset FiniteProbability LightSpanners
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

/-- Actual measured rational output, with a computable repetition schedule.
Every host-list iteration is charged; accuracy and the output bound are
conclusions of the independent 1/f assignment law, rather than premises. -/
theorem exists_measured_two_approximate_seed_high_probability
    (G Q : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℚ)
    (q f h k s : ℕ) (eps : ℚ)
    (hQ : IsFTConnectivityPreserver G Q q)
    (happrox : ∀ R, IsMinimumFTPreserver G R (fun e => (w e:ℝ)) q →
      totalWeight Q (fun e => (w e:ℝ)) ≤ 2*totalWeight R (fun e => (w e:ℝ)))
    (hbudget : 2*f+h≤q+1) (hf : 2≤f) (hh : 0<h) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ R : SimpleGraph (Fin n), IsMinimumFTPreserver G R (fun e => (w e:ℝ)) q ∧
      ∃ F : Fin (q+1) → SimpleGraph (Fin n),
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        ∀ hostIndices : List (ForestComponentIndex F),
          hostIndices.toFinset = (univ : Finset (ForestComponentIndex F)) →
          (CorrectedVoting.executionLaw (V:=Fin n) (J:=ForestComponentIndex F) f hf
            (CorrectedVoting.polynomialRepetitions (Fintype.card (Fin n)) s)
            (input G Q (fun e => (w e:ℝ)))).prob (fun a =>
              let result := CorrectedExecution.edgesWork hostIndices Q.edgeFinset w hw
                (paperStretch eps k) (CorrectedVoting.componentEligible univ F)
                (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) h
                (input G Q (fun e => (w e:ℝ)))
              ¬(IsEFTSpanner G (edgeGraph result.1) (fun e => (w e:ℝ))
                  (paperStretch eps k:ℝ) f ∧
                competitiveLightness (edgeGraph result.1) R (fun e => (w e:ℝ)) ≤
                  2+256*(f:ℝ)*extremalLightness n ((paperStretch eps k:ℝ)+1)/h ∧
                result.2 ≤ 1+(input G Q (fun e => (w e:ℝ))).length*
                  (hostIndices.length*(CorrectedVoting.polynomialRepetitions (Fintype.card (Fin n)) s*
                    (distanceBudget n+2)+5)+4))) ≤ ((n:ℝ)^s)⁻¹ := by
  classical
  let wr : Sym2 (Fin n) → ℝ := fun e => (w e:ℝ)
  have hepsR : 0 < (eps:ℝ) := by exact_mod_cast heps
  have hwR : ∀ e, 0 ≤ wr e := by
    intro e
    change 0 ≤ (w e:ℝ)
    exact_mod_cast hw e
  have hwposR : ∀ e∈G.edgeSet, 0 < wr e := by
    intro e he
    change 0 < (w e:ℝ)
    exact_mod_cast hwpos e he
  obtain ⟨R,hR⟩ := exists_minimum_preserver G wr q
  obtain ⟨F,hF,hgood⟩ := CorrectedVoting.exists_constructed_voting_weight
    hQ hbudget wr (eps:ℝ) k hf hh hk hepsR hwR hwposR
  refine ⟨R,hR,F,hF,?_⟩
  intro hostIndices hIndices
  apply (measured_failure_probability_le hostIndices hIndices G Q R w hw
    (paperStretch eps k) (CorrectedVoting.componentEligible univ F)
    (CorrectedVoting.componentHost F) (CorrectedVoting.polynomialRepetitions (Fintype.card (Fin n)) s) f h
    (2+256*(f:ℝ)*extremalLightness n ((paperStretch eps k:ℝ)+1)/h) _).trans
  have hprob := CorrectedVoting.polynomial_inaccurate_probability G Q wr
    ((1+(eps:ℝ))*(2*k-1)) q f h s hf hQ F
  simp only [Fintype.card_fin] at hprob
  apply (Law.prob_mono _ ?_).trans hprob
  intro a hbad hacc
  apply hbad
  obtain ⟨hsp,hweight⟩ := hgood (CorrectedVoting.assignmentTape a) hacc
  simp only [Fintype.card_fin] at hweight
  refine ⟨by simpa only [paperStretch_cast] using hsp,?_⟩
  have hL := extremalLightness_nonneg n (actual_threshold_gt_two hepsR hk)
  have hC : 0≤1+128*(f:ℝ)*extremalLightness n
      ((1+(eps:ℝ))*(2*k-1)+1)/h := by positivity
  simp only [paperStretch_cast]
  by_cases hz : totalWeight R wr=0
  · dsimp [wr] at hz
    simp only [competitiveLightness,hz,div_zero]
    positivity
  · have hn : 0≤totalWeight R wr := by
      unfold totalWeight
      exact sum_nonneg (fun e _ => hwR e)
    have hp : 0<totalWeight R wr := lt_of_le_of_ne hn (Ne.symm hz)
    apply (div_le_iff₀ hp).mpr
    calc
      _ ≤ (1+128*(f:ℝ)*extremalLightness n
          ((1+(eps:ℝ))*(2*k-1)+1)/h)*totalWeight Q wr := hweight
      _ ≤ (1+128*(f:ℝ)*extremalLightness n
          ((1+(eps:ℝ))*(2*k-1)+1)/h)*(2*totalWeight R wr) :=
        mul_le_mul_of_nonneg_left (happrox R hR) hC
      _ = _ := by ring

end LightEFTSpanners.CorrectedRuntime
