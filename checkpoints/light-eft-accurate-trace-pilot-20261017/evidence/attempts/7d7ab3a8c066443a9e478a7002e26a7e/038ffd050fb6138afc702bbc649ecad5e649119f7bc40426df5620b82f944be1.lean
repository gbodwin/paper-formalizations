import LightEFTSpanners.NativeForestCardinality
import Mathlib.Data.Set.Card

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*}

/-- The sharp finite connected-edge count certifies a true native tree, even
when the input representation permits loops and parallel identities. An actual
spanning tree is first constructed, then finite set equality proves it uses
all original edges. Native simplicity is a consequence, not a hidden premise. -/
theorem native_all_bridges_of_connected_card (G : Graph V E) [Finite G.vertexSet]
    [Finite G.edgeSet] (hc : G.toSimpleGraph.Connected)
    (hcard : Nat.card G.edgeSet+1=Nat.card G.vertexSet) :
    ∀ e∈G.edgeSet,G.IsBridge e := by
  obtain ⟨F,hF,hforest,_,hFcard⟩ := exists_native_spanning_tree G hc
  have hcardEq : Nat.card F=Nat.card G.edgeSet := by omega
  have hset : F=G.edgeSet := Set.eq_of_subset_of_ncard_le hF
    (by change Nat.card G.edgeSet≤Nat.card F; omega) (Set.toFinite _)
  simpa only [hset,Graph.restrict_self] using hforest

/-- A finite native tree is equivalently genuine connectedness together with
the exact original-edge count. This characterization is safe for multigraphs. -/
theorem native_tree_iff_connected_card (G : Graph V E) [Finite G.vertexSet]
    [Finite G.edgeSet] :
    ((∀ e∈G.edgeSet,G.IsBridge e) ∧ G.toSimpleGraph.Connected) ↔
      G.toSimpleGraph.Connected ∧ Nat.card G.edgeSet+1=Nat.card G.vertexSet := by
  constructor
  · rintro ⟨hb,hc⟩
    exact ⟨hc,native_tree_card G hb hc⟩
  · rintro ⟨hc,hcard⟩
    exact ⟨native_all_bridges_of_connected_card G hc hcard,hc⟩
end LightEFTSpanners.MultigraphCuts
