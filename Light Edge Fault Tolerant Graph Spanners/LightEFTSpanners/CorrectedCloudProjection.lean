import LightEFTSpanners.CorrectedCloudConstruction
import LightSpanners.CycleProjection

/-! Projection deletes internal cloud steps rather than treating them as edges
of the core simple graph. This is the arbitrary-real-stretch part of the
corrected Theorem 34, before any weight counting or extremal argument. -/
namespace LightEFTSpanners.CorrectedCloud
open SimpleGraph LightSpanners Finset

/-- A walk avoiding all copies of a core edge projects to a walk avoiding that
edge. Internal cloud steps have nonnegative cost and disappear. -/
theorem exists_projected_walk {m p : ℕ} {G : SimpleGraph (Fin m)}
    {H : SimpleGraph (Fin m × Fin p)} (hHG : H ≤ graph G p)
    (w : Sym2 (Fin m) → ℝ) (W : Sym2 (Fin m × Fin p) → ℝ)
    (hW : ∀ e ∈ H.edgeSet, 0 ≤ W e)
    (hcross : ∀ a b : Fin m × Fin p, G.Adj a.1 b.1 →
      W s(a,b) = w s(a.1,b.1))
    (e : Sym2 (Fin m)) {a b : Fin m × Fin p} (r : H.Walk a b)
    (havoid : ∀ d ∈ r.edges, Sym2.map Prod.fst d ≠ e) :
    ∃ q : (G.deleteEdges {e}).Walk a.1 b.1,
      walkWeight w q ≤ walkWeight W r := by
  induction r with
  | nil => exact ⟨.nil, by simp⟩
  | @cons a z b haz r ih =>
    obtain ⟨q,hq⟩ := ih (fun d hd => havoid d (by simp [hd]))
    have hcost : 0 ≤ W s(a,z) := hW _ ((mem_edgeSet H).mpr haz)
    by_cases heq : a.1 = z.1
    · refine ⟨q.copy heq.symm rfl, ?_⟩
      have hcopy : walkWeight w (q.copy heq.symm rfl) = walkWeight w q := by
        simp [walkWeight]
      rw [hcopy, walkWeight_cons]
      linarith
    · have hcore : G.Adj a.1 z.1 := by
        rcases hHG haz with h | h
        · exact (heq h.1).elim
        · exact h
      have hdel : (G.deleteEdges {e}).Adj a.1 z.1 :=
        deleteEdges_adj.mpr ⟨hcore, by
          simpa only [Set.mem_singleton_iff, Sym2.map_mk] using
            havoid s(a,z) (by simp)⟩
      refine ⟨.cons hdel q, ?_⟩
      simp only [walkWeight_cons, hcross a z hcore]
      linarith

/-- Weighted girth rules out every sufficiently short detour, including
non-simple walks and arbitrary real stretch. -/
theorem deleted_edge_walk_too_heavy {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {w : Sym2 V → ℝ} {t : ℝ}
    (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    (hg : WeightedGirthAbove G w (t+1)) {u v : V} (huv : G.Adj u v)
    (r : (G.deleteEdges {s(u,v)}).Walk u v) :
    t * w s(u,v) < walkWeight w r := by
  let q := (r.reverse.mapLe (deleteEdges_le {s(u,v)})).bypass
  have hnot : s(u,v) ∉ q.edges := by
    intro he
    have he' := (r.reverse.mapLe (deleteEdges_le {s(u,v)})).edges_bypass_sublist_edges.subset he
    have hr : s(u,v) ∈ r.reverse.edges := by simpa using he'
    have := r.reverse.edges_subset_edgeSet hr
    simp only [edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff,
      not_true_eq_false, and_false] at this
  have hc : (Walk.cons huv q).IsCycle :=
    (q.cons_isCycle_iff huv).mpr
      ⟨(r.reverse.mapLe (deleteEdges_le {s(u,v)})).bypass_isPath,hnot⟩
  have hcycle := hg u (.cons huv q) hc s(u,v) (by simp)
  have hq := walkWeight_bypass_le_on_edges w hw
    (r.reverse.mapLe (deleteEdges_le {s(u,v)}))
  have hreverse : walkWeight w r.reverse = walkWeight w r := by
    simp [walkWeight, List.map_reverse]
  simp only [walkWeight_mapLe, hreverse] at hq
  change walkWeight w q ≤ walkWeight w r at hq
  simp only [walkWeight_cons] at hcycle
  nlinarith

end LightEFTSpanners.CorrectedCloud
