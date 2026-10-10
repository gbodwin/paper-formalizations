import MinorFreeSpanners.DenseMinorNeighborhood
import MinorFreeSpanners.RobustSubgraph
import MinorFreeSpanners.RobustCliqueConstruction
import MinorFreeSpanners.CliqueDensityBudget

/-! An elementary O(h log h) density threshold for an actual complete minor.
This does not assert the sharper cited O(h sqrt(log h)) threshold, nor the
separate small-subgraph density increment required by the spanner theorem. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem clique_minor_of_logarithmic_density (G : SimpleGraph V) (h : ℕ)
    (hh : 0 < h) (hn : 0 < Fintype.card V)
    (hG : (6*cliqueDensityScale h)*Fintype.card V ≤ G.edgeFinset.card) :
    Nonempty (MinorModel (⊤ : SimpleGraph (Fin h)) G) := by
  classical
  let D := cliqueDensityScale h
  have hD : 0 < D := cliqueDensityScale_pos hh
  obtain ⟨n,M,v,⟨N⟩,hpos,hsize,hmin⟩ :=
    exists_dense_minor_neighborhood G (6*D) (by omega) hn hG
  let H := M.graph.induce (M.graph.neighborSet v)
  let : Nonempty (M.graph.neighborSet v) := Fintype.card_pos_iff.mp hpos
  have hsize' : Fintype.card (M.graph.neighborSet v) ≤ 12*D := by omega
  rcases robust_or_small_robust_induced H D hsize' hmin with hrob | ⟨A,hA,hAsize,⟨P⟩,hAmin,hArob⟩
  · obtain ⟨Q⟩ := robust_core_clique_minor H D h hD hsize'
      (fun x => (by
        change 4*D ≤ (M.graph.induce (M.graph.neighborSet v)).degree x
        have hx := hmin x
        omega)) hrob
      (cliqueDensityScale_cover_budget h _ hsize')
    exact ⟨Q.comp N⟩
  · let : Nonempty A := ⟨⟨hA.choose,hA.choose_spec⟩⟩
    have hAc : Fintype.card (A : Set (M.graph.neighborSet v)) ≤ 12*D := by
      calc
        _ = A.card := Fintype.card_of_finset' A (fun _ => Iff.rfl)
        _ ≤ 12*D := by omega
    obtain ⟨Q⟩ := robust_core_clique_minor (H.induce (A : Set (M.graph.neighborSet v))) D h hD hAc
      hAmin hArob (cliqueDensityScale_cover_budget h _ hAc)
    exact ⟨(Q.comp P).comp N⟩

/-- The resulting explicit edge bound for every finite excluded-minor graph,
including the empty host. -/
theorem CliqueMinorFree.edge_count_le_logarithmic {G : SimpleGraph V} {h : ℕ}
    (hfree : CliqueMinorFree G h) (hh : 0 < h) :
    G.edgeFinset.card ≤ (6*cliqueDensityScale h)*Fintype.card V := by
  by_cases hn : 0 < Fintype.card V
  · by_contra hnot
    exact hfree (clique_minor_of_logarithmic_density G h hh hn (by omega))
  · have hzero : Fintype.card V = 0 := by omega
    have he := G.card_edgeFinset_le_card_choose_two
    simpa [hzero] using he

end MinorFreeSpanners
