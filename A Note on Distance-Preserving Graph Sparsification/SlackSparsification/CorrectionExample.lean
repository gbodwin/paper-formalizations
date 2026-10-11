import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-! A genuine seven-vertex unweighted counterexample to the equality in the
first line of the Theorem 12 routing calculation. This does not refute the
+4 bound: replacing the equality by the triangle inequality repairs the step. -/
namespace SlackSparsification.CorrectionExample
open SimpleGraph

def H : SimpleGraph (Fin 7) := fromEdgeSet
  (↑({s(0,1), s(1,2), s(2,3), s(3,4), s(4,5), s(5,6), s(6,0)} : Finset (Sym2 (Fin 7))))

def G : SimpleGraph (Fin 7) := H ⊔ fromEdgeSet (↑({s(1,4)} : Finset (Sym2 (Fin 7))))

instance : DecidableRel H.Adj := by unfold H; infer_instance
instance : DecidableRel G.Adj := by unfold G; infer_instance

theorem H_le_G : H ≤ G := le_sup_left

theorem H_dist_01 : H.edist 0 1 = 1 := edist_eq_one_iff_adj.mpr (by decide)

theorem H_dist_04 : H.edist 0 4 = 3 := by
  let p : H.Walk 0 4 := .cons (by decide) (.cons (u := 6) (v := 5) (by decide)
    (.cons (u := 5) (v := 4) (by decide) .nil))
  have hu : H.edist 0 4 ≤ 3 := by simpa [p] using p.edist_le
  have hl : 2 < H.edist 0 4 := by
    apply two_lt_edist_iff.mpr
    refine ⟨by decide, by decide, ?_⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    have hc : ∀ v : Fin 7, ¬(H.Adj 0 v ∧ H.Adj 4 v) := by decide
    intro v hv
    exact hc v ((mem_commonNeighbors H).mp hv)
  exact le_antisymm hu (by have hh := Order.add_one_le_of_lt hl; norm_num at hh; exact hh)

theorem H_dist_14 : H.edist 1 4 = 3 := by
  let p : H.Walk 1 4 := .cons (by decide) (.cons (u := 2) (v := 3) (by decide)
    (.cons (u := 3) (v := 4) (by decide) .nil))
  have hu : H.edist 1 4 ≤ 3 := by simpa [p] using p.edist_le
  have hl : 2 < H.edist 1 4 := by
    apply two_lt_edist_iff.mpr
    refine ⟨by decide, by decide, ?_⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    have hc : ∀ v : Fin 7, ¬(H.Adj 1 v ∧ H.Adj 4 v) := by decide
    intro v hv
    exact hc v ((mem_commonNeighbors H).mp hv)
  exact le_antisymm hu (by have hh := Order.add_one_le_of_lt hl; norm_num at hh; exact hh)

theorem G_dist_01 : G.edist 0 1 = 1 := edist_eq_one_iff_adj.mpr (by decide)
theorem G_dist_14 : G.edist 1 4 = 1 := edist_eq_one_iff_adj.mpr (by decide)
theorem G_dist_04 : G.edist 0 4 = 2 := by
  apply edist_eq_two_iff.mpr
  exact ⟨by decide, by decide, 1, by decide⟩

/-- Vertex 1 lies on a shortest 0–4 path in G, yet the corresponding route
is strictly longer than the shortest 0–4 distance in its subgraph H. -/
theorem printed_equality_fails :
    H ≤ G ∧ G.edist 0 1 + G.edist 1 4 = G.edist 0 4 ∧
      H.edist 0 4 < H.edist 0 1 + H.edist 1 4 := by
  refine ⟨H_le_G, ?_, ?_⟩
  · norm_num [G_dist_01, G_dist_14, G_dist_04]
  · norm_num [H_dist_04, H_dist_01, H_dist_14]

end SlackSparsification.CorrectionExample
