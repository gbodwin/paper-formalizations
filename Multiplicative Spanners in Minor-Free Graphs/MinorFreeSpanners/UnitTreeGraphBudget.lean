import MinorFreeSpanners.LowGraphBudget

/-! The literal graph edge set is partitioned into low and heavy edges.
Both charges use the same actual unit spanning tree and canonical credit. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem unit_tree_graph_budget {V : Type*} [Fintype V]
    {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (t r h : ℕ) (ht : 4096≤t) (hr : 1≤r) (hh : 0<h)
    (hT : T≤G) (hTree : T.IsTree) (hunit : ∀ e∈T.edgeSet,w e=1)
    (hfree : CliqueMinorFree G h) (hG : WeightedGirthAbove G w (2*(r:ℝ)*(1+2000/(t:ℝ))))
    (hw : ∀ e∈G.edgeSet,0≤w e) :
    (∑ e∈G.edgeFinset,w e)≤
      (42*(Nat.log 2 t+1:ℕ)+1)*canonicalPhaseCredit t r h*(T.edgeFinset.card:ℝ) := by
  by_cases hz : T.edgeFinset.card=0
  · have hg := (canonical_phase_girth t r 1 ht hr le_rfl).1
    have hb : (∑ e∈G.edgeFinset,w e)≤0 := by
      apply Finset.sum_nonpos
      intro e he
      have hu := edge_weight_le_unit_spanning_budget hT hTree.connected hunit hg hG hw e
        (G.mem_edgeFinset.mp he)
      simpa [hz] using hu
    simpa [hz] using hb
  · have hlo := low_graph_budget t r h ht hr hh hTree (by omega) hfree hG hw
    have hhi := heavy_graph_budget t r h ht hr hh hT hTree hunit hfree hG hw
    have hsplit := Finset.sum_filter_add_sum_filter_not G.edgeFinset
      (fun e => (t:ℝ)≤w e) w
    simp only [not_le] at hsplit
    nlinarith only [hlo,hhi,hsplit]

end MinorFreeSpanners
