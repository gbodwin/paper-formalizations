import LightEFTSpanners.NativeBridgeSemantics
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Removing an unordered endpoint pair removes at least the corresponding
original edge identity, even when there are parallel identities. -/
theorem simple_deleted_le_native_deleted (G : Graph V E) {e : E}
    {u v : G.vertexSet} (he : G.IsLink e u.val v.val) :
    G.toSimpleGraph.deleteEdges {s(u,v)} ≤ (G.deleteEdges {e}).toSimpleGraph := by
  intro x y hxy
  obtain ⟨hxy,hn⟩ := deleteEdges_adj.mp hxy
  obtain ⟨hne,f,hf⟩ := hxy
  refine ⟨hne,f,hf,?_⟩
  intro hfe
  have hfe' : f=e := Set.mem_singleton_iff.mp hfe
  subst f
  apply hn
  apply Set.mem_singleton_iff.mpr
  rcases he.eq_and_eq_or_eq_and_eq hf with ⟨hx,hy⟩ | ⟨hy,hx⟩
  · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext hx.symm,Subtype.ext hy.symm⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext hx.symm,Subtype.ext hy.symm⟩)

/-- For a genuine simple native graph, deletion commutes with forgetting edge
identities. The simplicity hypothesis is essential for the reverse inclusion. -/
theorem native_deleted_le_simple_deleted (G : Graph V E) [G.Simple] {e : E}
    {u v : G.vertexSet} (he : G.IsLink e u.val v.val) :
    (G.deleteEdges {e}).toSimpleGraph ≤ G.toSimpleGraph.deleteEdges {s(u,v)} := by
  intro x y hxy
  obtain ⟨hne,f,hf,hn⟩ := hxy
  apply deleteEdges_adj.mpr
  refine ⟨⟨hne,f,hf⟩,?_⟩
  intro hpair
  have hp := Sym2.eq_iff.mp (Set.mem_singleton_iff.mp hpair)
  rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact hn (Set.mem_singleton_iff.mpr (hf.eq he))
  · exact hn (Set.mem_singleton_iff.mpr (hf.eq he.symm))

/-- Actual native bridges imply genuine acyclicity of the surviving adjacency
forest. This theorem is not the false converse for arbitrary multigraphs. -/
theorem acyclic_of_all_edges_bridge (G : Graph V E)
    (hbridge : ∀ e∈G.edgeSet,G.IsBridge e) : G.toSimpleGraph.IsAcyclic := by
  apply isAcyclic_iff_forall_adj_isBridge.mpr
  intro u v huv
  obtain ⟨_,e,he⟩ := huv
  apply isBridge_iff.mpr
  intro hr
  exact (bridge_iff_not_reachable_delete G he).mp (hbridge e he.edge_mem)
    (hr.mono (simple_deleted_le_native_deleted G he))

/-- The correct native forest characterization explicitly rules out loops and
parallel edges before using ordinary simple-graph acyclicity. -/
theorem all_edges_bridge_iff (G : Graph V E) :
    (∀ e∈G.edgeSet,G.IsBridge e) ↔ G.Simple ∧ G.toSimpleGraph.IsAcyclic := by
  refine ⟨fun h => ⟨simple_of_all_edges_bridge G h,acyclic_of_all_edges_bridge G h⟩,?_⟩
  rintro ⟨hs,ha⟩ e he
  let : G.Simple := hs
  obtain ⟨u,v,huv⟩ := Graph.exists_isLink_of_mem_edgeSet he
  apply (bridge_iff_not_reachable_delete G huv).mpr
  intro hr
  have hne : (⟨u,huv.left_mem⟩:G.vertexSet)≠⟨v,huv.right_mem⟩ :=
    fun h => huv.ne (congrArg Subtype.val h)
  have hadj : G.toSimpleGraph.Adj ⟨u,huv.left_mem⟩ ⟨v,huv.right_mem⟩ := ⟨hne,e,huv⟩
  exact (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp ha hadj))
    (hr.mono (native_deleted_le_simple_deleted G huv))
end LightEFTSpanners.MultigraphCuts
