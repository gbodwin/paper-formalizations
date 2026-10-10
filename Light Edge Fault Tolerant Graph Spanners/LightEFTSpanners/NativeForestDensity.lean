import LightEFTSpanners.NativeForestCardinality

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*}

/-- A genuinely disconnected finite forest has at least two fewer edges than
vertices. The proof extends the actual forest to a strict spanning tree. -/
theorem simple_forest_card_of_not_reachable (H : SimpleGraph V) [Finite V]
    (hforest : H.IsAcyclic) {a b : V} (hnot : ¬H.Reachable a b) :
    Nat.card H.edgeSet+2≤Nat.card V := by
  classical
  let : Nonempty V := ⟨a⟩
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨T,hHT,_,hT⟩ := (connected_top (V:=V)).exists_isTree_le_of_le_of_isAcyclic
    (show H≤(⊤:SimpleGraph V) from le_top) hforest
  have hlt : H<T := lt_of_le_of_ne hHT (by
    intro heq
    exact hnot ((congrArg (fun K : SimpleGraph V => K.Reachable a b) heq).mpr
      (hT.connected.preconnected a b)))
  have hcards := Finset.card_lt_card (edgeFinset_strict_mono hlt)
  have htree := hT.card_edgeFinset
  have hHcard : Nat.card H.edgeSet=H.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card,edgeFinset_card]
  rw [hHcard,Nat.card_eq_fintype_card]
  omega

/-- The disconnected-forest count retains original native edge identities and
actual vertices; it uses the proved simplicity/edge bijection, not projection
counts on a multigraph that still contains parallel cycles. -/
theorem native_forest_card_of_not_reachable (G : Graph V E) [Finite G.vertexSet]
    (hforest : ∀ e∈G.edgeSet,G.IsBridge e) {a b : G.vertexSet}
    (hnot : ¬G.toSimpleGraph.Reachable a b) :
    Nat.card G.edgeSet+2≤Nat.card G.vertexSet := by
  let : G.Simple := simple_of_all_edges_bridge G hforest
  rw [native_simple_card_edges G]
  exact simple_forest_card_of_not_reachable G.toSimpleGraph
    (acyclic_of_all_edges_bridge G hforest) hnot

/-- Enough original edges in a disconnected native graph on a finite actual
vertex domain force a real
nonbridge edge. This is the cycle-forcing obligation used by the tree-packing
proof; no cycle or exchange witness is assumed. -/
theorem native_exists_nonbridge_of_dense_disconnected (G : Graph V E)
    [Finite G.vertexSet] {a b : G.vertexSet}
    (hnot : ¬G.toSimpleGraph.Reachable a b)
    (hdense : Nat.card G.vertexSet≤Nat.card G.edgeSet+1) :
    ∃ e∈G.edgeSet,¬G.IsBridge e := by
  classical
  by_contra! hall
  have hsmall := native_forest_card_of_not_reachable G hall hnot
  omega
end LightEFTSpanners.MultigraphCuts
