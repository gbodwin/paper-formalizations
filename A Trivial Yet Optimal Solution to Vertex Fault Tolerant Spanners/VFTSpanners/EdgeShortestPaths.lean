import VFTSpanners.EdgeFault

namespace VFTSpanners
open SimpleGraph Finset
open scoped ENNReal
variable {V : Type*} [DecidableEq V] [Fintype V]
attribute [local instance] Classical.propDecidable

/-- Finite nonnegative weighted graphs have a minimum-weight fault-avoiding
walk whenever any such walk exists. This also covers zero-weight edges. -/
theorem exists_minimum_edge_walk (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (F : Finset (Sym2 V)) (u v : V)
    (hex : ∃ p : G.Walk u v, EdgeAvoids F p) :
    ∃ q : G.Walk u v, EdgeAvoids F q ∧
      ∀ p : G.Walk u v, EdgeAvoids F p → walkWeight w q ≤ walkWeight w p := by
  classical
  let P : Finset (G.Path u v) := univ.filter (fun p => EdgeAvoids F p.val)
  have hpath (p : G.Walk u v) (hp : EdgeAvoids F p) : p.toPath ∈ P := by
    exact mem_filter.mpr ⟨mem_univ _,fun x hx => hp x (p.edges_toPath_subset_edges hx)⟩
  have hnon : P.Nonempty := by
    obtain ⟨p,hp⟩ := hex
    exact ⟨p.toPath,hpath p hp⟩
  obtain ⟨q,hq,hmin⟩ := exists_min_image P (fun p => walkWeight w p.val) hnon
  refine ⟨q.val,(mem_filter.mp hq).2,?_⟩
  intro p hp
  exact (hmin p.toPath (hpath p hp)).trans (walkWeight_bypass_le w hw p)

theorem exists_walk_attaining_edgeDistance (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (F : Finset (Sym2 V)) (u v : V)
    (hex : ∃ p : G.Walk u v, EdgeAvoids F p) :
    ∃ q : G.Walk u v, EdgeAvoids F q ∧
      edgeFaultDistance G w F u v = ENNReal.ofReal (walkWeight w q) := by
  obtain ⟨q,hq,hmin⟩ := exists_minimum_edge_walk G w hw F u v hex
  refine ⟨q,hq,le_antisymm ?_ ?_⟩
  · exact iInf_le (fun p : {p : G.Walk u v // EdgeAvoids F p} =>
      ENNReal.ofReal (walkWeight w p.val)) ⟨q,hq⟩
  · exact le_iInf fun p => ENNReal.ofReal_le_ofReal (hmin p.val p.property)

/-- The walk-existence test used in `edgeGreedyEdges` is exactly a shortest-distance
test; it is not an assumption about shortest paths or a substitute algorithm. -/
theorem edgeDistance_le_iff_exists_walk (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (F : Finset (Sym2 V)) (u v : V) (t : ℝ) (ht : 0 ≤ t) :
    edgeFaultDistance G w F u v ≤ ENNReal.ofReal t ↔
      ∃ p : G.Walk u v, EdgeAvoids F p ∧ walkWeight w p ≤ t := by
  classical
  constructor
  · intro hd
    have hex : ∃ p : G.Walk u v, EdgeAvoids F p := by
      by_contra hn
      have : IsEmpty {p : G.Walk u v // EdgeAvoids F p} :=
        ⟨fun p => hn ⟨p.val,p.property⟩⟩
      have htop : edgeFaultDistance G w F u v = ⊤ := by simp [edgeFaultDistance]
      rw [htop, top_le_iff] at hd
      exact ENNReal.ofReal_ne_top hd
    obtain ⟨q,hq,heq⟩ := exists_walk_attaining_edgeDistance G w hw F u v hex
    rw [heq] at hd
    exact ⟨q,hq,(ENNReal.ofReal_le_ofReal_iff ht).mp hd⟩
  · rintro ⟨p,hp,hcost⟩
    exact (iInf_le (fun p : {p : G.Walk u v // EdgeAvoids F p} =>
      ENNReal.ofReal (walkWeight w p.val)) ⟨p,hp⟩).trans (ENNReal.ofReal_le_ofReal hcost)

/-- Precise correspondence of the formal greedy test to Algorithm 1. -/
theorem edgeCovered_iff_distance (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (k f : ℕ) (e : Sym2 V) :
    EdgeCovered G w k f e ↔ ∀ u v, s(u,v) = e →
      ∀ F : Finset (Sym2 V), F.card ≤ f → e ∉ F →
        edgeFaultDistance G w F u v ≤ ENNReal.ofReal ((k : ℝ)*w e) := by
  simp only [EdgeCovered, edgeDistance_le_iff_exists_walk G w hw _ _ _ _
    (mul_nonneg (Nat.cast_nonneg _) (hw e))]

/-- Before an input edge is processed it is absent from the current graph.
Consequently allowing the fault set to contain the queried edge, as in the
paper's pseudocode, gives exactly the same greedy test. -/
theorem edgeCovered_iff_all_faults_of_absent (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (k f : ℕ) (e : Sym2 V) (he : e ∉ G.edgeSet) :
    EdgeCovered G w k f e ↔ ∀ u v, s(u,v) = e →
      ∀ F : Finset (Sym2 V), F.card ≤ f →
        ∃ p : G.Walk u v, EdgeAvoids F p ∧ walkWeight w p ≤ (k : ℝ)*w e := by
  constructor
  · intro hc u v huv F hF
    obtain ⟨p,hp,hw⟩ := hc u v huv (F.erase e)
      ((card_erase_le).trans hF) (notMem_erase _ _)
    refine ⟨p,?_,hw⟩
    intro d hd hdF
    have hde : d ≠ e := fun h => he (h ▸ p.edges_subset_edgeSet hd)
    exact hp d hd (mem_erase.mpr ⟨hde,hdF⟩)
  · intro hc u v huv F hF _
    exact hc u v huv F hF

end VFTSpanners
