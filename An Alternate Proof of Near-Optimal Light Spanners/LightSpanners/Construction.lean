import LightSpanners.Distance
import LightSpanners.MinimumTree

namespace LightSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

noncomputable def greedyInput (G : SimpleGraph V) (w : Sym2 V → ℝ) : List (Sym2 V) :=
  G.edgeFinset.toList.mergeSort (fun e d => decide (w d ≤ w e))

omit [DecidableEq V] in
theorem greedyInput_perm (G : SimpleGraph V) (w : Sym2 V → ℝ) :
    (greedyInput G w).Perm G.edgeFinset.toList := List.mergeSort_perm _ _

omit [DecidableEq V] in
@[simp] theorem mem_greedyInput (G : SimpleGraph V) (w : Sym2 V → ℝ) (e : Sym2 V) :
    e ∈ greedyInput G w ↔ e ∈ G.edgeFinset := by
  rw [(greedyInput_perm G w).mem_iff, mem_toList]

omit [DecidableEq V] in
theorem greedyInput_sorted (G : SimpleGraph V) (w : Sym2 V → ℝ) :
    (greedyInput G w).Pairwise (fun e d => w d ≤ w e) := by
  have h := List.pairwise_mergeSort
    (le := fun e d : Sym2 V => decide (w d ≤ w e))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; exact hbc.trans hab)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) G.edgeFinset.toList
  simpa only [greedyInput, decide_eq_true_eq] using h

omit [DecidableEq V] in
theorem greedyInput_nondiag (G : SimpleGraph V) (w : Sym2 V → ℝ) :
    ∀ e ∈ greedyInput G w, ¬ e.IsDiag := fun e he =>
  G.not_isDiag_of_mem_edgeFinset ((mem_greedyInput G w e).mp he)

@[simp] theorem greedyInput_graph (G : SimpleGraph V) (w : Sym2 V → ℝ) :
    edgeGraph (greedyInput G w).toFinset = G := by
  have h : (greedyInput G w).toFinset = G.edgeFinset := by ext e; simp
  rw [h, edgeGraph, coe_edgeFinset, fromEdgeSet_edgeSet]

noncomputable def greedyOutput (G : SimpleGraph V) (w : Sym2 V → ℝ) (t : ℝ) :
    SimpleGraph V := edgeGraph (greedyEdges w t (greedyInput G w))

/-- Greedy-stage guarantees; the subsequent lightness argument remains open. -/
theorem greedyOutput_preliminaries (G : SimpleGraph V) (w : Sym2 V → ℝ) (t : ℝ)
    (ht : 1 ≤ t) (hw : ∀ e, 0 ≤ w e) (hconn : G.Connected) :
    IsSpanner G (greedyOutput G w t) w t ∧
      (∀ u v, weightedDistance (greedyOutput G w t) w u v ≤
        ENNReal.ofReal t * weightedDistance G w u v) ∧
      WeightedGirthAbove (greedyOutput G w t) w (t + 1) ∧
      ∃ T : SimpleGraph V, T ≤ greedyOutput G w t ∧ IsMinimumSpanningTree G T w := by
  have hspan : IsSpanner G (greedyOutput G w t) w t := by
    simpa only [greedyInput_graph, greedyOutput] using
      greedy_isSpanner w t ht hw (greedyInput G w) (greedyInput_nondiag G w)
  refine ⟨hspan, hspan.distance_le (by linarith), ?_, ?_⟩
  · exact greedy_weightedGirth w t (by linarith) (greedyInput G w) (greedyInput_sorted G w)
  · have hc : (edgeGraph (greedyInput G w).toFinset).Connected := by
      simpa only [greedyInput_graph] using hconn
    simpa only [greedyInput_graph, greedyOutput] using greedy_contains_mst w t
      (greedyInput G w) (greedyInput_nondiag G w) (greedyInput_sorted G w) hc

end LightSpanners
