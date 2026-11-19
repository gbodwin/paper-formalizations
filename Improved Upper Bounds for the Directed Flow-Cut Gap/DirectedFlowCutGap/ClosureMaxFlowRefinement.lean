import DirectedFlowCutGap.IntegralFlowRelabeling
import DirectedFlowCutGap.ResidualMaxFlowCutProgram
import DirectedFlowCutGap.MinimumClosureOptimizer

/-!
# Exact minimum-closure cuts from the physical flow solver

The closure budget suffices for the relabeled network. A closed set gives
the separating cut used in the proof. The output mask follows the
original retained cut, independently of the internal numerical order.
-/

namespace DirectedFlowCutGap.ClosureMaxFlowRefinement

open scoped BigOperators
open IntegralNetworkFlow MinimumClosureProblem MinimumClosureCut MinimumClosureOptimizer BinaryArithmetic

variable {A : Type*} [Fintype A] [DecidableEq A] {N : ℕ}

theorem capacity_bound (P : Problem A) (u v : Vertex A) : capacity P u v≤2*budget P+1 := by
  have weight (a : A) : (P.cost a).natAbs≤budget P := by
    exact Finset.single_le_sum (f := fun a => (P.cost a).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  have positive_le (a : A) : positive P a≤budget P := by
    have eq := Int.toNat_add_toNat_neg_eq_natAbs (P.cost a)
    have h := weight a
    unfold positive
    omega
  have negative_le (a : A) : negative P a≤budget P := by
    have eq := Int.toNat_add_toNat_neg_eq_natAbs (P.cost a)
    have h := weight a
    unfold negative
    omega
  cases u with
  | inl a =>
    cases v with
    | inl b =>
      simp only [capacity,barrier]
      split <;> omega
    | inr b =>
      cases b
      · simp [capacity]
      · have h := positive_le a
        simp only [capacity,barrier]
        split <;> omega
  | inr b =>
    cases v with
    | inr v =>
      cases b <;> cases v <;> simp [capacity]
    | inl a =>
      cases b
      · have h := negative_le a
        simp only [capacity,barrier]
        split <;> omega
      · simp [capacity]

abbrev renamedCapacity (P : Problem A) (e : Vertex A ≃ Fin N) : Capacity (Fin N) :=
  IntegralFlowRelabeling.capacity e (capacity P)

def separatingSet (T : Finset A) (e : Vertex A ≃ Fin N) : Finset (Fin N) :=
  (lift T).map e.toEmbedding

omit [Fintype A] in
theorem source_mem (T : Finset A) (e : Vertex A ≃ Fin N) : e source ∈ separatingSet T e := by
  simp [separatingSet]

omit [Fintype A] in
theorem sink_not_mem (T : Finset A) (e : Vertex A ≃ Fin N) : e sink ∉ separatingSet T e := by
  simp [separatingSet]

theorem renamed_budget (P : Problem A) (T : Finset A) (closed : P.IsClosed T) (e : Vertex A ≃ Fin N) :
    cutCapacity (renamedCapacity P e) (separatingSet T e) ≤ budget P := by
  unfold renamedCapacity separatingSet
  rw [IntegralFlowRelabeling.cut_capacity,cutCapacity_lift P T closed]
  exact finiteCost_le_budget P T

theorem renamed_widths (P : Problem A) (e : Vertex A ≃ Fin N) (B : ℕ)
    (bound : (2*budget P+1).size≤B) :
    ∀ u v,(max (renamedCapacity P e u v) (renamedCapacity P e v u)).size≤B := by
  intro u v
  apply Nat.le_trans (Nat.size_le_size ?_) bound
  exact max_le (capacity_bound P (e.symm u) (e.symm v)) (capacity_bound P (e.symm v) (e.symm u))

def mask (P : Problem A) (e : Vertex A ≃ Fin N) (E : ResidualSearch.Enumeration (Vertex A)) : Bits :=
  let f := runFlow P (finiteResidualSearch E (capacity P) source sink)
  (List.finRange N).map fun v => decide (e.symm v ∈ finiteResidualCut E f)

theorem reference_mask (P : Problem A) (T : Finset A) (closed : P.IsClosed T)
    (e : Vertex A ≃ Fin N) (E : ResidualSearch.Enumeration (Vertex A))
    (D : ResidualSearch.Enumeration (Fin N)) :
    ResidualMaxFlowCutProgram.referenceCut (c:=renamedCapacity P e) (s:=e source) (t:=e sink) D
      (separatingSet T e) = mask P e E := by
  let X := separatingSet T e
  let find := finiteResidualSearch D (renamedCapacity P e) (e source) (e sink)
  let base := IntegralNetworkFlow.run find (Flow.zero (renamedCapacity P e) (e source) (e sink))
    (cutCapacity (renamedCapacity P e) X)
  let f := runFlow P (finiteResidualSearch E (capacity P) source sink)
  let g := IntegralFlowRelabeling.flow e f
  have gStop : ¬Nonempty (SimplePath g.residual (e source) (e sink)) := by
    intro h
    exact runFlow_no_path P (finiteResidualSearch E (capacity P) source sink) T closed
      ((IntegralFlowRelabeling.path_iff e f source sink).mpr h)
  have baseStop : ¬Nonempty (SimplePath base.residual (e source) (e sink)) :=
    run_stopped_at_cut_budget find X (source_mem T e) (sink_not_mem T e)
  have same := finiteResidualCut_eq_of_terminal D D base g baseStop gStop
  change ((List.finRange N).map fun v => decide (v ∈ finiteResidualCut D base)) =
    (List.finRange N).map fun v => decide (e.symm v ∈ finiteResidualCut E f)
  rw [same]
  apply List.map_congr_left
  intro v _
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq,decide_eq_true_eq,mem_finiteResidualCut_iff_no_walk,
    mem_finiteResidualCut_iff_no_walk,← nonempty_simplePath_iff_directedWalk,
    ← nonempty_simplePath_iff_directedWalk]
  have paths := IntegralFlowRelabeling.path_iff e f (e.symm v) sink
  rw [Equiv.apply_symm_apply] at paths
  exact (not_congr paths).symm

end DirectedFlowCutGap.ClosureMaxFlowRefinement
