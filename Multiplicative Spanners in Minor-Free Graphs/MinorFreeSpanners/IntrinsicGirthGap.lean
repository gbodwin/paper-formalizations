import MinorFreeSpanners.Greedy

/-! Replacement-path inequalities intrinsic to weighted girth. These remain
valid after normalization without assuming the normalized graph is still the
output of an edge-ordered greedy algorithm. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners
variable {V : Type*} {G : SimpleGraph V} {w : Sym2 V → ℝ}

lemma walkWeight_clamp_zero (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    {u v : V} (p : G.Walk u v) :
    walkWeight (fun e => max 0 (w e)) p = walkWeight w p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [walkWeight_cons, ih, max_eq_right (hw _ ((mem_edgeSet G).mpr h))]

lemma walkWeight_bypass_le_of_edge_nonnegative [DecidableEq V]
    (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e) {u v : V} (p : G.Walk u v) :
    walkWeight w p.bypass ≤ walkWeight w p := by
  have h := walkWeight_bypass_le (fun e => max 0 (w e)) (fun _ => le_max_left _ _) p
  simpa only [walkWeight_clamp_zero hw] using h

/-- Every alternative walk avoiding an edge is longer than (g−1) times that
edge's weight. The proof extracts an actual simple cycle from its bypass. -/
theorem replacement_walk_gap [DecidableEq V] {g : ℝ}
    (hG : WeightedGirthAbove G w g) (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    {u v : V} (huv : G.Adj u v) (p : G.Walk u v) (he : s(u,v) ∉ p.edges) :
    (g - 1) * w s(u,v) < walkWeight w p := by
  have hnot : s(u,v) ∉ p.bypass.edges := fun h => he (p.edges_bypass_subset_edges h)
  have hc : (Walk.cons huv.symm p.bypass).IsCycle :=
    (Walk.cons_isCycle_iff _ _).mpr ⟨p.bypass_isPath, by simpa only [Sym2.eq_swap] using hnot⟩
  have hb := walkWeight_bypass_le_of_edge_nonnegative hw p
  have hg := hG v (Walk.cons huv.symm p.bypass) hc s(u,v) (by simp [Sym2.eq_swap])
  simp only [walkWeight_cons, Sym2.eq_swap] at hg
  nlinarith

end MinorFreeSpanners
