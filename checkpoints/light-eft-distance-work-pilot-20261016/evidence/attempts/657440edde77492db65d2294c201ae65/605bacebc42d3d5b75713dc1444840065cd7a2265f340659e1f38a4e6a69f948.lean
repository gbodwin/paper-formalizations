import LightEFTSpanners.MultigraphFaultConnectivity

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Failure of actual post-deletion reachability gives a genuine separating
vertex cut contained in the deleted original identities. No finite domain,
cardinality premise, flow theorem or path-packing oracle is used. -/
theorem not_reachable_cut_subset (G : Graph V E) (F : Set E)
    {a b : G.vertexSet}
    (hnot : ¬(G.deleteEdges F).toSimpleGraph.Reachable a b) :
    ∃ S : Set V,a.val∈S ∧ b.val∉S ∧ G.edgeCut S⊆F := by
  classical
  let H := (G.deleteEdges F).toSimpleGraph
  let S : Set V := {v | ∃ hv : v∈G.vertexSet,H.Reachable a ⟨v,hv⟩}
  have ha : a.val∈S := ⟨a.property,Reachable.refl a⟩
  have hb : b.val∉S := by rintro ⟨_,h⟩; exact hnot h
  refine ⟨S,ha,hb,?_⟩
  intro e he
  obtain ⟨u,v,hlink,hu,hv⟩ := he
  by_contra hn
  have hne : (⟨u,hlink.left_mem⟩:G.vertexSet)≠⟨v,hlink.right_mem⟩ := by
    intro heq
    have huv : u=v := congrArg Subtype.val heq
    exact hv (huv ▸ hu)
  have hadj : H.Adj ⟨u,hlink.left_mem⟩ ⟨v,hlink.right_mem⟩ := ⟨hne,e,hlink,hn⟩
  obtain ⟨_,huR⟩ := hu
  exact hv ⟨hlink.right_mem,huR.trans hadj.reachable⟩

/-- Mathlib's native edge-cut bridge notion agrees with actual disconnection
of an edge's endpoints after deleting that original identity. Loops are never
bridges, and a parallel surviving edge correctly prevents disconnection. -/
theorem bridge_iff_not_reachable_delete (G : Graph V E) {e : E} {u v : V}
    (hlink : G.IsLink e u v) :
    G.IsBridge e ↔ ¬(G.deleteEdges {e}).toSimpleGraph.Reachable
      ⟨u,hlink.left_mem⟩ ⟨v,hlink.right_mem⟩ := by
  constructor
  · rintro ⟨S,hcut⟩ hr
    have he : e∈G.edgeCut S := by rw [hcut]; exact Set.mem_singleton e
    have hr' : (G.deleteEdges (G.edgeCut S)).toSimpleGraph.Reachable
        ⟨u,hlink.left_mem⟩ ⟨v,hlink.right_mem⟩ :=
      (congrArg (fun F : Set E => (G.deleteEdges F).toSimpleGraph.Reachable
        ⟨u,hlink.left_mem⟩ ⟨v,hlink.right_mem⟩) hcut).mpr hr
    have hs := after_cut_reachable_sides G S hr'
    rcases hlink.mem_edgeCut_iff.mp he with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · exact hv (hs.mp hu)
    · exact hu (hs.mpr hv)
  · intro hn
    obtain ⟨S,hu,hv,hsub⟩ := not_reachable_cut_subset G {e} hn
    refine ⟨S,Set.Subset.antisymm hsub ?_⟩
    exact Set.singleton_subset_iff.mpr ⟨u,v,hlink,hu,hv⟩

/-- If every actual native edge is a bridge, loops and parallel edges are
impossible. This establishes the genuine graph semantics needed before
identifying such a forest with its ordinary simple adjacency graph. -/
theorem simple_of_all_edges_bridge (G : Graph V E)
    (hbridge : ∀ e∈G.edgeSet,G.IsBridge e) : G.Simple := by
  refine {not_isLoopAt := ?_,eq_of_isLink := ?_}
  · intro e x hloop
    have hn := (bridge_iff_not_reachable_delete G
      (show G.IsLink e x x from hloop)).mp (hbridge e hloop.edge_mem)
    exact hn (Reachable.refl _)
  · intro e f x y he hf
    obtain ⟨S,hcut⟩ := hbridge e he.edge_mem
    have hecut : e∈G.edgeCut S := by rw [hcut]; exact Set.mem_singleton e
    have hfcut : f∈G.edgeCut S := hf.mem_edgeCut_iff.mpr (he.mem_edgeCut_iff.mp hecut)
    have hfe : f=e := by simpa [hcut] using hfcut
    exact hfe.symm
end LightEFTSpanners.MultigraphCuts
