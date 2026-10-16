import LightEFTSpanners.NativeQuotientReachability
import LightEFTSpanners.NativeForestDensity

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V W E : Type*} [Finite W]
attribute [local instance] Classical.propDecidable

/-- A dense disconnected quotient along actual connected fibers forces a
crossing original edge with a genuine alternate path after its own deletion.
Thus the edge crosses the supplied terminal partition and lies on a real
original cycle; no cycle or exchange edge is a premise. -/
theorem exists_crossing_nonbridge_of_dense_quotient (G : Graph V E) (f : V → W)
    (hc : ∀ a b : G.vertexSet,f a=f b →
      (blockGraph G.toSimpleGraph (Setoid.ker (fun a : G.vertexSet => f a))).Reachable a b)
    {a b : G.vertexSet} (hnot : ¬G.toSimpleGraph.Reachable a b)
    (hdense : Nat.card (f '' G.vertexSet)≤Nat.card (crossingQuotient G f).edgeSet+1) :
    ∃ e u v,∃ he : G.IsLink e u v, f u≠f v ∧ ¬G.IsBridge e ∧
      (G.deleteEdges {e}).toSimpleGraph.Reachable ⟨u,he.left_mem⟩ ⟨v,he.right_mem⟩ := by
  classical
  have hn := not_reachable_crossingQuotient G f hc hnot
  obtain ⟨e,he,hnb⟩ := native_exists_nonbridge_of_dense_disconnected
    (crossingQuotient G f) hn hdense
  have hmem := he
  obtain ⟨_,u,v,huv,huvne⟩ := hmem
  have hnbG : ¬G.IsBridge e := fun hb =>
    hnb ((crossing_bridge_map G f hc huv huvne hb).anti_of_mem (Graph.restrict_le ..) he)
  have hr : (G.deleteEdges {e}).toSimpleGraph.Reachable
      ⟨u,huv.left_mem⟩ ⟨v,huv.right_mem⟩ := by
    by_contra hnr
    exact hnbG ((bridge_iff_not_reachable_delete G huv).mpr hnr)
  exact ⟨e,u,v,huv,huvne,hnbG,hr⟩
end LightEFTSpanners.MultigraphCuts
