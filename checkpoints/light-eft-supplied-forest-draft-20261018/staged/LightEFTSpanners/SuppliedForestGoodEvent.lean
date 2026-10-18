import LightEFTSpanners.VotingOutput
import LightEFTSpanners.VotingOutputWeight
import LightEFTSpanners.ForestComponentPacking
import LightEFTSpanners.ConstructedVotingHosts
import LightEFTSpanners.ConnectivityOptimum

/-!
Staged proof draft only: not compiled, checked, or promoted into the accepted graph.
The family and tape in the conclusion are exactly the supplied family and tape.
No seed-connectivity, minimum-seed, sampling-law or runtime conclusion is asserted.
-/
namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners HostCounting
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- A supplied forest certificate gives the deterministic reached-state good
event. The direct eligible-host count replaces any separate fault-budget
inequality. The raw bound and its zero-weight consequence are retained. -/
theorem voting_good_event_of_supplied_forests
    (G Q : SimpleGraph V) (hQG : Q ≤ G)
    (q f h k : ℕ) (w : Sym2 V → ℝ) (eps : ℝ)
    (F : Fin (q+1) → SimpleGraph V)
    (hF : ∀ i, F i ≤ Q ∧ (F i).IsAcyclic)
    (hcount : ∀ e ∈ G.edgeFinset \ Q.edgeFinset,
      2*f+h ≤ (componentEligible univ F e).card)
    (hcong : ∀ d : Sym2 V,
      (hosts (univ : Finset (Fin (q+1))) (fun i => (F i).edgeFinset) d).card ≤ 2)
    (hf : 0 < f) (hh : 0 < h) (hk : 0 < k) (heps : 0 < eps)
    (hw : ∀ e, 0 ≤ w e) (hwpos : ∀ e ∈ G.edgeSet, 0 < w e)
    (tape : Tape V (ForestComponentIndex F))
    (hacc : AccurateTrace Q.edgeFinset w ((1+eps)*(2*k-1)) f
      (componentEligible univ F) (componentHost F) tape h (input G Q w)) :
    let t : ℝ := (1+eps)*(2*k-1)
    let H := output G Q w t (componentEligible univ F) (componentHost F) tape h
    let B : ℝ := 1+64*(f:ℝ)*extremalLightness (Fintype.card V) (t+1)/h
    IsEFTSpanner G H w t f ∧
      totalWeight H w ≤ B * totalWeight Q w ∧
      (totalWeight Q w = 0 → totalWeight H w = 0) ∧
      competitiveLightness H Q w ≤ B := by
  classical
  let t : ℝ := (1+eps)*(2*k-1)
  let H := output G Q w t (componentEligible univ F) (componentHost F) tape h
  let B : ℝ := 1+64*(f:ℝ)*extremalLightness (Fintype.card V) (t+1)/h
  change IsEFTSpanner G H w t f ∧
    totalWeight H w ≤ B * totalWeight Q w ∧
    (totalWeight Q w = 0 → totalWeight H w = 0) ∧
    competitiveLightness H Q w ≤ B
  have ht : 1 ≤ t := by
    have hthreshold := actual_threshold_gt_two heps hk
    dsimp only [t]
    linarith
  have hfull (d : Sym2 V) :
      (hosts (forestComponentIndices univ F) (componentHost F) d).card ≤ 2 :=
    (forest_component_congestion univ F d).trans (hcong d)
  have hlocal (e d : Sym2 V) :
      (hosts (componentEligible univ F e) (componentHost F) d).card ≤ 2 := by
    apply le_trans (card_le_card ?_) (hfull d)
    intro p hp
    obtain ⟨hp,hd⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨(mem_filter.mp hp).1,hd⟩
  have hhost (p : ForestComponentIndex F) : componentHost F p ⊆ Q.edgeFinset :=
    edgeFinset_mono ((component_tree_le (F p.1) p.2).trans (hF p.1).1)
  have hcorrect : IsEFTSpanner G H w t f := by
    exact output_isEFTSpanner G Q hQG w t f h
      (componentEligible univ F) (componentHost F) tape hf ht hw
      (fun _ _ p _ => hhost p) hcount (fun e _ d => hlocal e d) hacc
  have hweight : totalWeight H w ≤ B * totalWeight Q w := by
    let A : ForestComponentIndex F → Type _ := fun p => p.2
    let j : ∀ p, A p ↪ V := fun p => componentEmbedding (F p.1) p.2
    let T : ∀ p, SimpleGraph (A p) := fun p => p.2.toSimpleGraph
    apply voting_output_weight_bound G Q hQG w eps k f h hk heps hf hh
      (forestComponentIndices univ F) j T (componentEligible univ F) tape
      (fun p _ => component_isTree (hF p.1).2 p.2)
      (fun p _ => (component_tree_le (F p.1) p.2).trans (hF p.1).1)
      (fun _ _ => filter_subset _ _) (fun _ _ p hp => (mem_filter.mp hp).2)
      (fun d _ => hfull d) hwpos hacc
  have hzero : totalWeight Q w = 0 → totalWeight H w = 0 := by
    intro hz
    have hnonneg : 0 ≤ totalWeight H w := by
      unfold totalWeight
      exact sum_nonneg (fun e _ => hw e)
    have hupper : totalWeight H w ≤ 0 := by
      simpa only [hz,mul_zero] using hweight
    exact le_antisymm hupper hnonneg
  have hB : 0 ≤ B := by
    have hLambda := extremalLightness_nonneg (Fintype.card V)
      (actual_threshold_gt_two heps hk)
    dsimp only [B,t]
    positivity
  have hratio : competitiveLightness H Q w ≤ B := by
    by_cases hz : totalWeight Q w = 0
    · have houtzero : totalWeight H w = 0 := hzero hz
      simpa only [competitiveLightness,hz,houtzero,div_zero] using hB
    · have hQnonneg : 0 ≤ totalWeight Q w := by
        unfold totalWeight
        exact sum_nonneg (fun e _ => hw e)
      have hQpos : 0 < totalWeight Q w := lt_of_le_of_ne hQnonneg (Ne.symm hz)
      exact (div_le_iff₀ hQpos).mpr hweight
  exact ⟨hcorrect,hweight,hzero,hratio⟩

end LightEFTSpanners.SampledGreedy
