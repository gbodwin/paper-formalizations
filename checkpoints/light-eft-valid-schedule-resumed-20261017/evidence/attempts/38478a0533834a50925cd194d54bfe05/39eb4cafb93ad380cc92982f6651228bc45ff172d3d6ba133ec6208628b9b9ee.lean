import LightEFTSpanners.ExtremalReindex

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

/-- An actual positive MST edge can be split into equal halves. This adds
exactly one vertex, preserves the graph/MST ratio exactly, and cannot decrease
weighted girth. Kruskal supplies the needed bottleneck tree internally. -/
theorem exists_order_succ_same_lightness {G T : SimpleGraph V} {w : Sym2 V → ℝ} {g : ℝ}
    (hT : IsMinimumSpanningTree G T w) (hw : ∀ e∈G.edgeSet,0<w e)
    (hg : WeightedGirthAbove G w g) (hg0 : 0≤g) (hn : 2≤Fintype.card V) :
    ∃ G' T' : SimpleGraph (Option V), ∃ w' : Sym2 (Option V) → ℝ,
      IsMinimumSpanningTree G' T' w' ∧ (∀ e∈G'.edgeSet,0<w' e) ∧
      WeightedGirthAbove G' w' g ∧ lightness G' T' w'=lightness G T w := by
  classical
  obtain ⟨K,hKG,hK,hopt⟩ := exists_bottleneck_spanning_tree G w (hT.2.1.connected.mono hT.1)
  have hKm := minimumSpanningTree_of_bottleneck hK hKG hopt
  have hc := hK.card_edgeFinset
  have hne : K.edgeFinset.Nonempty := card_pos.mp (by omega)
  obtain ⟨d,hd⟩ := hne
  obtain ⟨u,v⟩ := d
  have huv : K.Adj u v := mem_edgeFinset.mp hd
  have hwuv := hw s(u,v) (G.mem_edgeSet.mpr (hKG huv))
  let a := w s(u,v)/2
  have ha : 0<a := by dsimp [a];positivity
  have hsum : a+a=w s(u,v) := by dsimp [a];ring
  refine ⟨subdivideEdge G u v,subdivideEdge K u v,subdivideWeight w u a a,
    subdivision_isMinimumSpanningTree hK hKG hopt huv hsum ha.le ha.le,
    subdivideWeight_positive_edges w hw ha ha,
    hg.subdivideEdge (hKG huv) w hsum ha.le ha.le hg0,?_⟩
  rw [lightness_subdivideEdge hKG huv w hsum]
  exact lightness_mst_independent hKm hT
end LightEFTSpanners
