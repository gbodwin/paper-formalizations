import LightEFTSpanners.SubdivisionPreserver
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace LightEFTSpanners.ParallelSubdivision
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

theorem cycle_base_edge_count (m : ℕ) : (cycleGraph (m+3)).edgeFinset.card=m+3 := by
  have hs := (cycleGraph (m+3)).sum_degrees_eq_twice_card_edges
  simp only [cycleGraph_degree_three_le,sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at hs
  omega

/-- Exact vertex accounting for the actual parallel-subdivided cycle. -/
theorem cycle_vertex_count (m f : ℕ) :
    Fintype.card (Vertex (I:=Fin f) (cycleGraph (m+3)))=(m+3)+(m+3)*f := by
  simp only [Vertex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  rw [← edgeFinset_card,cycle_base_edge_count]

/-- The unit edges of the actual source cycle construction form a genuine
(2f−1)-fault connectivity preserver, even with arbitrary additional core edges.
Fault-isolated branch vertices are allowed and are handled by full reachability
semantics rather than by assuming the entire certificate remains connected. -/
theorem cycle_unit_graph_isFTPreserver (m f : ℕ) (hf : 0<f)
    (D : SimpleGraph (Fin (m+3))) :
    IsFTConnectivityPreserver
      (graph (I:=Fin f) (cycleGraph (m+3)) ⊔ coreGraph (cycleGraph (m+3)) D)
      (graph (I:=Fin f) (cycleGraph (m+3))) (2*f-1) := by
  classical
  have hadj : (cycleGraph (m+3)).Adj 0 1 := by
    rw [cycleGraph_adj]
    exact Or.inr (by simp)
  let : Nonempty (cycleGraph (m+3)).edgeSet :=
    ⟨⟨s((0:Fin (m+3)),1),(mem_edgeSet _).mpr hadj⟩⟩
  have hcycles : (cycleGraph (m+3)).IsCycles := by
    intro v _
    rw [ncard_neighborSet,cycleGraph_degree_three_le]
  apply unit_graph_isFTPreserver (cycleGraph (m+3)) cycleGraph_preconnected
  · intro e he
    rcases e with ⟨u,v⟩
    exact not_not_intro (hcycles.reachable_deleteEdges ((mem_edgeSet _).mp he))
  · simp only [Fintype.card_fin]
    omega
end LightEFTSpanners.ParallelSubdivision
