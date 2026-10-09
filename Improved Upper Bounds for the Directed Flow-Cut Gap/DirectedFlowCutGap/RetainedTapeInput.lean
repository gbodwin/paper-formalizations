import DirectedFlowCutGap.IntegerAdaptiveExecution
import DirectedFlowCutGap.FiniteGridSampler
import Mathlib.Data.List.NodupEquivFin

/-!
# Materializing exact finite tapes for retained integer execution

The active enumeration scans a fixed row-major list of original labels and
filters it by the stored Boolean mask. Both directions are executable: lookup
uses `List.get`, and its inverse uses `List.idxOf`. The supplied finite tapes
then materialize the actual order and cell array consumed by the retained
controller. No mathematical state or arbitrary finite enumeration is evaluated.
-/
namespace DirectedFlowCutGap.RetainedTapeInput

open scoped NNReal
open CandidateSchedule CandidateSchedule.State RetainedGridState
open FinitePermutationSampler

/-- The fixed row-major list of original demand labels. -/
def allPairs (n : ℕ) : List (Pair n) :=
  List.ofFn (finProdFinEquiv.symm : Fin (n * n) → Pair n)

theorem allPairs_nodup (n : ℕ) : (allPairs n).Nodup :=
  List.nodup_ofFn.mpr finProdFinEquiv.symm.injective

@[simp] theorem mem_allPairs {n : ℕ} (p : Pair n) : p ∈ allPairs n := by
  rw [allPairs, List.mem_ofFn]
  exact ⟨finProdFinEquiv p, finProdFinEquiv.symm_apply_apply p⟩

/-- One Boolean filter, with no deleted-label renumbering in the stored state. -/
def activeList {n : ℕ} (a : PairFlags n) : List (Pair n) :=
  (allPairs n).filter (flag a)

theorem activeList_nodup {n : ℕ} (a : PairFlags n) : (activeList a).Nodup :=
  (allPairs_nodup n).filter _

@[simp] theorem mem_activeList {n : ℕ} (a : PairFlags n) (p : Pair n) :
    p ∈ activeList a ↔ p ∈ remainingSet a := by
  simp [activeList]

theorem activeList_toFinset {n : ℕ} (a : PairFlags n) :
    (activeList a).toFinset = remainingSet a := by
  ext p
  simp

theorem activeList_length {n : ℕ} (a : PairFlags n) :
    (activeList a).length = Fintype.card ↥(remainingSet a) := by
  rw [Fintype.card_coe, ← activeList_toFinset a]
  exact (List.toFinset_card_of_nodup (activeList_nodup a)).symm

/-- A concrete active-label equivalence; all transports carry only proofs. -/
def activeEnum {n : ℕ} (a : PairFlags n) :
    Fin (Fintype.card ↥(remainingSet a)) ≃ ↥(remainingSet a) :=
  (finCongr (activeList_length a).symm).trans
    (((activeList_nodup a).getEquiv (activeList a)).trans
      { toFun := fun p => ⟨p.val, (mem_activeList a p.val).mp p.property⟩
        invFun := fun p => ⟨p.val, (mem_activeList a p.val).mpr p.property⟩
        left_inv := by intro p; rfl
        right_inv := by intro p; rfl })

/-- The primitive finite draws required by exactly the current active mask. -/
abbrev Tape {n : ℕ} (L : ℕ) (a : PairFlags n) :=
  FinitePermutationSampler.Tape (Fintype.card ↥(remainingSet a)) ×
    FiniteGridSampler.Cells L (Fintype.card ↥(remainingSet a))

/-- Materialized original-label order and retained two-dimensional cell array. -/
def materialize {n L : ℕ} (hL : 0 < L) (a : PairFlags n) (t : Tape L a) :
    IntegerAdaptiveExecution.Input n L :=
  let enum := activeEnum a
  { order := (labelOrder enum t.1).map Subtype.val
    cells := Vector.ofFn fun s => Vector.ofFn fun v =>
      if hp : (s, v) ∈ remainingSet a then
        FiniteGridSampler.labelCells enum t.2 ⟨(s, v), hp⟩
      else ⟨0, hL⟩ }

theorem materialize_cell {n L : ℕ} (hL : 0 < L) (a : PairFlags n)
    (t : Tape L a) (p : Pair n) (hp : p ∈ remainingSet a) :
    (materialize hL a t).cell p =
      FiniteGridSampler.labelCells (activeEnum a) t.2 ⟨p, hp⟩ := by
  simp [materialize, IntegerAdaptiveExecution.Input.cell, (mem_remainingSet a p).mp hp]

theorem materialize_order_nodup {n L : ℕ} (hL : 0 < L) (a : PairFlags n)
    (t : Tape L a) : (materialize hL a t).order.Nodup := by
  exact (labelOrder_nodup (activeEnum a) t.1).map Subtype.val_injective

theorem materialize_order_toFinset {n L : ℕ} (hL : 0 < L) (a : PairFlags n)
    (t : Tape L a) : (materialize hL a t).order.toFinset = remainingSet a := by
  ext p
  simp only [List.mem_toFinset, materialize, List.mem_map]
  constructor
  · rintro ⟨q, _, rfl⟩
    exact q.property
  · intro hp
    exact ⟨⟨p, hp⟩, mem_labelOrder (activeEnum a) t.1 ⟨p, hp⟩, rfl⟩

theorem materialize_order_length {n L : ℕ} (hL : 0 < L) (a : PairFlags n)
    (t : Tape L a) : (materialize hL a t).order.length = (remainingSet a).card := by
  rw [← materialize_order_toFinset hL a t]
  exact (List.toFinset_card_of_nodup (materialize_order_nodup hL a t)).symm

section Refinement
variable {n L : ℕ} {G : Digraph (Fin n)} {D : Finset (Pair n)}
variable {selector : FlexibleCandidateSchedule.FamilyProvider G D (L : ℝ≥0) → Prop}
variable {H : ∃ P, selector P}

/-- The epoch interpreter reads levels only at labels in its supplied list. -/
theorem run_eq_of_levels_on_order (r M : ℝ≥0)
    (u v : Pair n → AdaptiveEpoch.UnitLevel) (s : State G D (L : ℝ≥0))
    (order : List (Pair n)) (h : ∀ p ∈ order, u p = v p) :
    AdaptiveEpoch.run r M u s order = AdaptiveEpoch.run r M v s order := by
  induction order generalizing s with
  | nil => rfl
  | cons p ps ih =>
      simp only [AdaptiveEpoch.run]
      split_ifs with ha
      · have hr := congrArg (fun level : AdaptiveEpoch.UnitLevel =>
          s.round p ha.2 level.val level.property) (h p (by simp))
        rw [hr]
        rw [ih _ (fun q hq => h q (by simp [hq]))]
      · rfl

theorem materialize_epoch_eq (hL : 0 < L) [NeZero L] (R : ℕ)
    (s : Code G D L) (t : Tape L s.data.remaining) :
    AdaptiveEpoch.run (R : ℝ≥0) (interpret s).mass
        (IntegerAdaptiveExecution.levels hL (materialize hL s.data.remaining t))
        (interpret s) (materialize hL s.data.remaining t).order =
      FiniteGridSampler.midpointTapeEpoch (R : ℝ≥0) (interpret s)
        (activeEnum s.data.remaining) t := by
  apply run_eq_of_levels_on_order
  intro p hp
  have hm : p ∈ remainingSet s.data.remaining := by
    rw [← materialize_order_toFinset hL s.data.remaining t]
    exact List.mem_toFinset.mpr hp
  simp only [IntegerAdaptiveExecution.levels, materialize_cell hL _ _ _ hm]
  unfold FiniteGridSampler.midpointLevels
  rw [dite_eq_left (show p ∈ (interpret s).remaining from hm)]
  apply Subtype.ext
  rfl

/-- Equality includes both the complete mathematical state and actual cut count. -/
theorem scan_refines_midpoint (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R : ℕ) (c : Cache H)
    (t : Tape L c.state.data.remaining) :
    (⟨interpret (IntegerAdaptiveExecution.scan Q hL C R c.state.data.current
          (materialize hL c.state.data.remaining t).cell
          (materialize hL c.state.data.remaining t).order c).cache.state,
        (IntegerAdaptiveExecution.scan Q hL C R c.state.data.current
          (materialize hL c.state.data.remaining t).cell
          (materialize hL c.state.data.remaining t).order c).work.rounds⟩ :
      AdaptiveEpoch.Result G D (L : ℝ≥0)) =
      FiniteGridSampler.midpointTapeEpoch (R : ℝ≥0) (interpret c.state)
        (activeEnum c.state.data.remaining) t := by
  rw [IntegerAdaptiveExecution.scan_refines Q hL,
    IntegerAdaptiveExecution.scan_rounds_refine Q hL, ← interpret_mass]
  exact materialize_epoch_eq hL R c.state t

noncomputable section

/-- The retained cut interpreter has exactly the existing joint epoch law. -/
theorem scan_law (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R : ℕ) (c : Cache H) :
    (FiniteGridSampler.tapePMF (Fintype.card ↥(remainingSet c.state.data.remaining)) L).map
      (fun t => (⟨interpret (IntegerAdaptiveExecution.scan Q hL C R c.state.data.current
          (materialize hL c.state.data.remaining t).cell
          (materialize hL c.state.data.remaining t).order c).cache.state,
        (IntegerAdaptiveExecution.scan Q hL C R c.state.data.current
          (materialize hL c.state.data.remaining t).cell
          (materialize hL c.state.data.remaining t).order c).work.rounds⟩ :
        AdaptiveEpoch.Result G D (L : ℝ≥0))) =
      AdaptiveRounding.epochPMF (R : ℝ≥0) (interpret c.state) := by
  simp_rw [scan_refines_midpoint Q hL C R c]
  exact FiniteGridSampler.midpointTapeEpoch_law (R : ℝ≥0) (interpret c.state)
    (activeEnum c.state.data.remaining)
    (fun p => interpret_allWeightsOnGrid c.state p.val p.property)

end
end Refinement
end DirectedFlowCutGap.RetainedTapeInput
