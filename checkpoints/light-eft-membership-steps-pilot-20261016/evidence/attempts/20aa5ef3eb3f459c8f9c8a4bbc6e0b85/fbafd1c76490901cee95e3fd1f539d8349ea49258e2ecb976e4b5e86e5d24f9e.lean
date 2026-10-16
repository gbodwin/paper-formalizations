import LightEFTSpanners.NativeEdgeLevels
import LightEFTSpanners.NativeNonbridgeCore
import LightEFTSpanners.NativeExchangeConnectivity

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Deleting a genuine native nonbridge preserves every actual connection,
using the original edge identity rather than deleting its unordered pair. -/
theorem native_reachable_delete_nonbridge (G : Graph V E) {e : E}
    (hnb : ¬G.IsBridge e) {a b : G.vertexSet} (hr : G.toSimpleGraph.Reachable a b) :
    (G.deleteEdges {e}).toSimpleGraph.Reachable a b := by
  classical
  apply reachable_of_edge_routes _ _ (a:=a) (b:=b) ?_ hr
  intro x y hxy
  obtain ⟨hne,d,hd⟩ := hxy
  by_cases hde : d=e
  · subst d
    by_contra hnot
    exact hnb ((bridge_iff_not_reachable_delete G hd).mpr hnot)
  · exact (show (G.deleteEdges {e}).toSimpleGraph.Adj x y from
      ⟨hne,d,hd,by simpa using hde⟩).reachable

theorem native_connected_delete_nonbridge (G : Graph V E) {e : E}
    (hnb : ¬G.IsBridge e) (hc : G.toSimpleGraph.Connected) :
    (G.deleteEdges {e}).toSimpleGraph.Connected := by
  let : Nonempty (G.deleteEdges {e}).vertexSet := hc.nonempty
  refine ⟨?_⟩
  intro a b
  exact native_reachable_delete_nonbridge G hnb (hc.preconnected a b)

/-- If deleting an internal nonbridge has no replacement route inside a
partition block, some other native nonbridge necessarily leaves that block.
The witness is derived from the actual bridge-free alternate path. -/
theorem exists_external_nonbridge_of_no_block_route [Fintype E] (G : Graph V E)
    (R : Setoid G.vertexSet) {e : E} {a b : G.vertexSet}
    (he : G.IsLink e a.val b.val) (hnb : ¬G.IsBridge e)
    (hnot : ¬(blockGraph (G.deleteEdges {e}).toSimpleGraph R).Reachable a b) :
    ∃ d∈G.edgeSet,¬G.IsBridge d ∧ ¬edgeInside G R d := by
  classical
  by_contra! hall
  have hr := nonbridge_alternate_route_in_core G he hnb
  apply hnot
  apply hr.mono
  intro x y hxy
  obtain ⟨hne,d,⟨hnd,hd⟩,hde⟩ := hxy
  have hin := hall d hd.edge_mem hnd
  exact ⟨⟨hne,d,hd,hde⟩,(edgeInside_iff G R hd).mp hin⟩
end LightEFTSpanners.MultigraphCuts
