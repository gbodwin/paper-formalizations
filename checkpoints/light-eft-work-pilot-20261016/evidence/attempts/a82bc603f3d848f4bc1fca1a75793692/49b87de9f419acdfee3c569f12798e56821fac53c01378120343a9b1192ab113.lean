import LightEFTSpanners.ConstructedVotingHosts

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners HostCounting
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
attribute [local instance] Classical.propDecidable

omit [DecidableEq I] in
/-- Every actual edge of a component host has both endpoints in that host.
Consequently the per-edge eligible-host congestion already bounds the full
component family, even when the edge itself is a seed edge. -/
theorem component_full_congestion (indices : Finset I) (F : I → SimpleGraph V)
    (hcong : ∀ e d,(hosts (componentEligible indices F e) (componentHost F) d).card≤2)
    (d : Sym2 V) :
    (hosts (forestComponentIndices indices F) (componentHost F) d).card≤2 := by
  apply le_trans (card_le_card ?_) (hcong d d)
  intro p hp
  obtain ⟨hp,hd⟩ := mem_filter.mp hp
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨hp,?_⟩,hd⟩
  have heq := mapped_edgeFinset_at (componentEmbedding (F p.1) p.2) p.2.toSimpleGraph
    (inferInstance : Fintype (p.2.toSimpleGraph.map (componentEmbedding (F p.1) p.2)).edgeSet)
    (inferInstance : Fintype p.2.toSimpleGraph.edgeSet)
  change d∈(p.2.toSimpleGraph.map (componentEmbedding (F p.1) p.2)).edgeFinset at hd
  rw [heq] at hd
  obtain ⟨e,_,he⟩ := mem_map.mp hd
  exact ⟨e,he⟩
end LightEFTSpanners.SampledGreedy
