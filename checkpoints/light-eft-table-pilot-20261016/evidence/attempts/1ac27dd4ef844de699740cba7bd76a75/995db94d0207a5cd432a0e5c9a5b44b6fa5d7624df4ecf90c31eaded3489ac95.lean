import LightEFTSpanners.ConstructedSeededPacking
import LightEFTSpanners.ForestComponentPacking

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners HostCounting ParallelSubdivision EvenSplitting
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def componentHost (F : I → SimpleGraph V) (p : ForestComponentIndex F) :
    Finset (Sym2 V) := (p.2.toSimpleGraph.map (componentEmbedding (F p.1) p.2)).edgeFinset

noncomputable def componentEligible (indices : Finset I) (F : I → SimpleGraph V)
    (e : Sym2 V) : Finset (ForestComponentIndex F) :=
  (forestComponentIndices indices F).filter fun p =>
    ∃ d,(componentEmbedding (F p.1) p.2).sym2Map d=e

/-- Literal subtree hosts obtained from the internally constructed Eulerian
packing. Every missing input edge has q+1 eligible hosts, and original edge
congestion is at most two. No host family is an input to this theorem. -/
theorem exists_voting_forest_hosts {G Q : SimpleGraph V} {q : ℕ}
    (hQ : IsFTConnectivityPreserver G Q q) :
    ∃ F : Fin (q+1) → SimpleGraph V,
      (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
      (∀ e∈G.edgeFinset\Q.edgeFinset,
        q+1≤(componentEligible univ F e).card) ∧
      (∀ e,∀ p∈componentEligible univ F e,componentHost F p⊆Q.edgeFinset) ∧
      (∀ e d,(hosts (componentEligible univ F e) (componentHost F) d).card≤2) := by
  classical
  obtain ⟨T,hT,hd,hc⟩ := exists_simple_eulerian_forest_packing
    (graph (I:=Fin 2) Q) (q+1) (doubled_even_degrees Q)
  obtain ⟨F,hF,hr,hcong⟩ := exists_projected_forest_family Q
    (univ : Finset (Fin (q+1))) T (fun i _ => (hT i).1)
    (fun i _ j _ hij => hd hij)
  refine ⟨F,fun i => hF i (mem_univ _),?_,?_,?_⟩
  · intro e he
    obtain ⟨a,b⟩ := e
    obtain ⟨heG,heQ⟩ := mem_sdiff.mp he
    have hR := hQ.missing_edge_edgeReachable (mem_edgeFinset.mp heG)
      (fun hh => heQ (mem_edgeFinset.mpr hh))
    have hall (i : Fin (q+1)) : (F i).Reachable a b := by
      apply hr i (mem_univ _) a b
      apply hc i
      simpa [mul_comm] using core_edge_connectivity (I:=Fin 2) Q hR
    have hh := forest_component_endpoint_count (univ : Finset (Fin (q+1))) F a b
    simpa [componentEligible,hall] using hh
  · intro e p _
    exact edgeFinset_mono ((component_tree_le (F p.1) p.2).trans (hF p.1 (mem_univ _)).1)
  · intro e d
    apply le_trans (card_le_card ?_)
      ((forest_component_congestion (univ : Finset (Fin (q+1))) F d).trans ?_)
    · intro p hp
      obtain ⟨hp,hd⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨(mem_filter.mp hp).1,hd⟩
    · simpa only [hosts,mem_edgeFinset,Fintype.card_fin] using hcong d
end LightEFTSpanners.SampledGreedy
