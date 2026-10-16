import LightEFTSpanners.ConstructedVotingHosts
import LightEFTSpanners.VotingOutput
import LightEFTSpanners.RoundedCompetition

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- The actual forest/component hosts are obtained internally from an actual
q-fault connectivity preserver. For every empirical tape accurate on its own
reached states, the literal h-vote output is an f-EFT spanner. This is the
deterministic good-event implication, not a concentration or runtime claim. -/
theorem exists_constructed_voting_correctness {G Q : SimpleGraph V} {q f h : ℕ}
    (hQ : IsFTConnectivityPreserver G Q q) (hbudget : 2*f+h≤q+1)
    (w : Sym2 V → ℝ) (t : ℝ) (hf : 0<f) (ht : 1≤t) (hw : ∀ e,0≤w e) :
    ∃ F : Fin (q+1) → SimpleGraph V,
      (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
      ∀ tape : Tape V (ForestComponentIndex F),
        AccurateTrace Q.edgeFinset w t f (componentEligible univ F) (componentHost F) tape h
          (input G Q w) →
        IsEFTSpanner G (output G Q w t (componentEligible univ F) (componentHost F) tape h) w t f := by
  classical
  obtain ⟨F,hF,hcount,hsub,hcong⟩ := exists_voting_forest_hosts hQ
  refine ⟨F,hF,?_⟩
  intro tape hacc
  apply output_isEFTSpanner G Q hQ.1 w t f h (componentEligible univ F) (componentHost F) tape
    hf ht hw (fun e _ => hsub e) (fun e he => hbudget.trans (hcount e he))
    (fun e _ => hcong e) hacc

/-- Algorithm2's repaired one-vote insertion rule, with all packing premises
discharged. A supplied seed need only be a real2f-fault preserver. -/
theorem exists_algorithm_two_correctness {G Q : SimpleGraph V} {f : ℕ}
    (hQ : IsFTConnectivityPreserver G Q (2*f))
    (w : Sym2 V → ℝ) (t : ℝ) (hf : 0<f) (ht : 1≤t) (hw : ∀ e,0≤w e) :
    ∃ F : Fin (2*f+1) → SimpleGraph V,
      (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
      ∀ tape : Tape V (ForestComponentIndex F),
        AccurateTrace Q.edgeFinset w t f (componentEligible univ F) (componentHost F) tape 1
          (input G Q w) →
        IsEFTSpanner G (output G Q w t (componentEligible univ F) (componentHost F) tape 1) w t f :=
  exists_constructed_voting_correctness hQ (by omega) w t hf ht hw

/-- Algorithm3's repaired floor((2+eta)f) seed and floor(eta*f)+1 vote rule.
The exact rounding works for every positive eta, without a hidden upper cap. -/
theorem exists_algorithm_three_correctness {G Q : SimpleGraph V} {f : ℕ} {eta : ℝ}
    (hQ : IsFTConnectivityPreserver G Q ⌊(2+eta)*(f:ℝ)⌋₊) (heta : 0<eta)
    (w : Sym2 V → ℝ) (t : ℝ) (hf : 0<f) (ht : 1≤t) (hw : ∀ e,0≤w e) :
    ∃ F : Fin (⌊(2+eta)*(f:ℝ)⌋₊+1) → SimpleGraph V,
      (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
      ∀ tape : Tape V (ForestComponentIndex F),
        AccurateTrace Q.edgeFinset w t f (componentEligible univ F) (componentHost F) tape
          (⌊eta*(f:ℝ)⌋₊+1) (input G Q w) →
        IsEFTSpanner G
          (output G Q w t (componentEligible univ F) (componentHost F) tape (⌊eta*(f:ℝ)⌋₊+1)) w t f := by
  apply exists_constructed_voting_correctness hQ ?_ w t hf ht hw
  rw [rounded_fault_budget f heta.le]
  omega
end LightEFTSpanners.SampledGreedy
