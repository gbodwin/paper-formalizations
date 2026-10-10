import LightSpanners.MinimumTree

/-! A bottleneck spanning tree cannot contain all maximum-weight choices on a
cycle. This is the structural fact used when subdividing only heavy tree edges
in the reduction of Lemma 3.5. Equal-weight ties are explicitly allowed. -/
namespace LightSpanners
open SimpleGraph
variable {V : Type*} [DecidableEq V]

/-- For every edge of a cycle there is an edge outside a bottleneck tree on the
same cycle that is at least as heavy. The conclusion allows equality. -/
theorem exists_nontree_cycle_edge_ge {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (hT : T.IsTree) (hopt : HasBottleneckPaths G T w)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    {e : Sym2 V} (he : e ∈ p.edges) :
    ∃ f ∈ p.edges, f ∉ T.edgeSet ∧ w e ≤ w f := by
  classical
  by_cases heT : e ∈ T.edgeSet
  · obtain ⟨u, v, heq, q, _, hq⟩ := cycle_complement p hp w he
    subst e
    have hb : T.IsBridge s(u,v) :=
      isAcyclic_iff_forall_isBridge.mp hT.isAcyclic heT
    have hcut : ¬ (T.deleteEdges {s(u,v)}).Reachable v u :=
      fun h => hb h.symm
    obtain ⟨x, y, hxy, hfq, hfcut⟩ := exists_edge_not_reachable q hcut
    have hfe : s(x,y) ≠ s(u,v) := (hq _ hfq).2
    have hfT : s(x,y) ∉ T.edgeSet := by
      intro hf
      exact hfcut (Adj.reachable
        (deleteEdges_adj.mpr ⟨(mem_edgeSet T).mp hf, hfe⟩))
    obtain ⟨r, hr⟩ := hopt x y hxy
    have her : s(u,v) ∈ r.edges := by
      by_contra hn
      apply hfcut
      refine ⟨r.transfer (T.deleteEdges {s(u,v)}) ?_⟩
      intro d hd
      rw [edgeSet_deleteEdges]
      exact ⟨r.edges_subset_edgeSet hd, fun h => hn (h ▸ hd)⟩
    exact ⟨s(x,y), (hq _ hfq).1, hfT, hr _ her⟩
  · exact ⟨e, he, heT, le_rfl⟩

/-- A maximum-weight cycle edge can be selected outside the bottleneck tree. -/
theorem exists_nontree_cycle_max {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (hT : T.IsTree) (hopt : HasBottleneckPaths G T w)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) :
    ∃ f ∈ p.edges, f ∉ T.edgeSet ∧ ∀ e ∈ p.edges, w e ≤ w f := by
  classical
  have hne : p.edges.toFinset.Nonempty := by
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil p.edges
      (fun h => hp.not_nil (Walk.edges_eq_nil.mp h))
    exact ⟨e, List.mem_toFinset.mpr he⟩
  obtain ⟨e, he, hmax⟩ := p.edges.toFinset.exists_max_image w hne
  obtain ⟨f, hf, hfT, hef⟩ :=
    exists_nontree_cycle_edge_ge hT hopt p hp (List.mem_toFinset.mp he)
  exact ⟨f, hf, hfT, fun d hd => (hmax d (List.mem_toFinset.mpr hd)).trans hef⟩

end LightSpanners
