import LightEFTSpanners.VotingOutputWeight
import LightEFTSpanners.VotingComponentCongestion
import LightEFTSpanners.ConstructedVotingCorrectness

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners HostCounting
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- The same actual sampled-voting output is correct and light on its reached-
state accuracy event. All packing and tree-host premises are constructed from
an actual seed preserver. No supplied lightness or probability oracle occurs. -/
theorem exists_constructed_voting_weight {G Q : SimpleGraph V} {q f h : ℕ}
    (hQ : IsFTConnectivityPreserver G Q q) (hbudget : 2*f+h≤q+1)
    (w : Sym2 V → ℝ) (eps : ℝ) (k : ℕ) (hf : 0<f) (hh : 0<h) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ F : Fin (q+1) → SimpleGraph V,
      (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
      ∀ tape : Tape V (ForestComponentIndex F),
        AccurateTrace Q.edgeFinset w ((1+eps)*(2*k-1)) f
          (componentEligible univ F) (componentHost F) tape h (input G Q w) →
        IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1))
          (componentEligible univ F) (componentHost F) tape h) w ((1+eps)*(2*k-1)) f ∧
        totalWeight (output G Q w ((1+eps)*(2*k-1))
          (componentEligible univ F) (componentHost F) tape h) w≤
          (1+64*(f:ℝ)*extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)/h)*totalWeight Q w := by
  classical
  obtain ⟨F,hF,hcount,hsub,hcong⟩ := exists_voting_forest_hosts hQ
  refine ⟨F,hF,?_⟩
  intro tape hacc
  have ht : 1≤(1+eps)*(2*(k:ℝ)-1) := by
    have hh := actual_threshold_gt_two heps hk;linarith
  constructor
  · apply output_isEFTSpanner G Q hQ.1 w ((1+eps)*(2*k-1)) f h
      (componentEligible univ F) (componentHost F) tape hf ht hw
      (fun e _ => hsub e) (fun e he => hbudget.trans (hcount e he))
      (fun e _ => hcong e) hacc
  · let A : ForestComponentIndex F → Type _ := fun p => p.2
    let j : ∀ p,A p ↪ V := fun p => componentEmbedding (F p.1) p.2
    let T : ∀ p,SimpleGraph (A p) := fun p => p.2.toSimpleGraph
    apply voting_output_weight_bound G Q hQ.1 w eps k f h hk heps hf hh
      (forestComponentIndices univ F) j T (componentEligible univ F) tape
      (fun p _ => component_isTree (hF p.1).2 p.2)
      (fun p _ => (component_tree_le (F p.1) p.2).trans (hF p.1).1)
      (fun _ _ => filter_subset _ _) (fun _ _ p hp => (mem_filter.mp hp).2)
      (fun d _ => component_full_congestion univ F hcong d) hwpos hacc
end LightEFTSpanners.SampledGreedy
