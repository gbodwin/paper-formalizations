import Mathlib.Data.Fin.VecNotation
import OnlineReachabilityPreservers.BackwardCopyReturns

/-! A return that disappears after both frozen width cuts. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

local instance decidableLocalBefore {I V : Type*} [DecidableEq V]
    (paths : I → List V) (i : I) (x y : V) : Decidable (BeforeIn paths i x y) := by
  unfold BeforeIn
  infer_instance

def actualWidthReturnPaths : Fin 10 → List (Fin 12) :=
  ![[0,1,2,3,4,5],[0],[0],[0],[0],[5,0],[],[],[],[]]

theorem actualWidthReturnPaths_widths :
    let M := ∑ i, (actualWidthReturnPaths i).length
    M = 12 ∧ 4*M/12 = 4 ∧ 4*M/10 = 4 := by decide

private theorem actualWidthReturnPaths_reverse_reaches :
    (5 : Fin 12) ∈ reachIn (pathPrecedenceGraph actualWidthReturnPaths) 0 4 := by
  have returnEdge : Edge (pathPrecedenceGraph actualWidthReturnPaths) 5 0 := by
    simp only [Edge,pathPrecedenceGraph,mem_filter,mem_univ,true_and]
    exact ⟨5,by decide⟩
  exact reachIn_succ.mpr (Or.inr ⟨0,returnEdge,target_mem_reachIn _ _ 3⟩)

theorem actualWidthReturnPaths_old_fails :
    ¬ NoShortReturnAcrossWidthCuts actualWidthReturnPaths 4 7 := by
  intro safe
  have forward : BeforeIn actualWidthReturnPaths 0 0 5 := by decide
  have different : (actualWidthReturnPaths 0).idxOf 0/4 ≠ (actualWidthReturnPaths 0).idxOf 5/4 := by decide
  exact safe forward different actualWidthReturnPaths_reverse_reaches

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
theorem actualWidthReturnPaths_copied_succeeds :
    NoShortReturnAcrossCopiedWidthCuts actualWidthReturnPaths 4 4 7 := by
  unfold NoShortReturnAcrossCopiedWidthCuts
  dsimp only
  decide

private def actualForwardReturnVertices : Fin 3 → ListVertexBlockIndex actualWidthReturnPaths 4 :=
  ![⟨0,⟨0,by decide⟩⟩,⟨5,⟨0,by decide⟩⟩,⟨0,⟨1,by decide⟩⟩]

private def actualForwardReturnRows : Fin 2 → Fin 10 := ![0,5]

theorem actualWidthReturnPaths_forward_copy_return :
    ¬ NoShortSplitReturn (splitListVertices actualWidthReturnPaths 4) (·.fst) 4 := by
  intro safe
  have steps : ∀ i : Fin 2,
      BeforeIn (splitListVertices actualWidthReturnPaths 4) (actualForwardReturnRows i)
        (actualForwardReturnVertices i.castSucc) (actualForwardReturnVertices i.succ) := by decide
  have difference : actualForwardReturnVertices 0 ≠ actualForwardReturnVertices (Fin.last 2) := by decide
  exact difference (safe actualForwardReturnVertices actualForwardReturnRows (by decide) steps (by decide))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
theorem actualWidthReturnPaths_no_backward_copy_return :
    NoShortBackwardCopyReturn actualWidthReturnPaths 4 4 := by
  apply NoShortBackwardCopyReturn.of_reachIn
  decide

/-- The old graph's return meets every internal boundary of the long row. -/
theorem actualWidthReturnPaths_original_run_long :
    shortReturnRunLength actualWidthReturnPaths 7 0 0 = 6 := by
  have first : (actualWidthReturnPaths (0 : Fin 10)).idxOf (0 : Fin 12) = 0 := by decide
  have last : (actualWidthReturnPaths (0 : Fin 10)).idxOf (5 : Fin 12) = 5 := by decide
  have len : (actualWidthReturnPaths (0 : Fin 10)).length = 6 := by decide
  have before : BeforeIn actualWidthReturnPaths 0 0 5 := by decide
  have rankZero (x : Fin 12) (on : x ∈ actualWidthReturnPaths 0) :
      shortReturnCutRank actualWidthReturnPaths 7 0 x = 0 := by
    apply shortReturnCutRank_eq_of_cut (fun {_ _} _ h => (Nat.not_lt_zero _ h).elim) (Nat.zero_le _)
    intro cut positive fits safe
    have index := List.idxOf_lt_length_of_mem on
    rw [len] at index
    exact safe before (by simpa only [first] using positive) (by rw [last]; omega)
      actualWidthReturnPaths_reverse_reaches
  unfold shortReturnRunLength
  rw [List.filter_eq_self.mpr (fun x on => decide_eq_true (rankZero x on))]
  exact len

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem actualWidthReturnPaths_copied_steps_have_no_return :
    ∀ (i : Fin 10) (x y : ListVertexBlockIndex actualWidthReturnPaths 4),
      BeforeIn (splitListVertices actualWidthReturnPaths 4) i x y →
      y ∉ reachIn (listPiecePrecedenceGraph (splitListVertices actualWidthReturnPaths 4)) x 4 := by
  decide

/-- The very same input has only singleton or empty runs after copying. -/
theorem actualWidthReturnPaths_copied_runs_small (i : Fin 10) (r : ℕ) :
    copiedShortReturnRunLength actualWidthReturnPaths 4 7 i r ≤ 1 := by
  let rank (x : Fin 12) := copiedReturnCutRank actualWidthReturnPaths 4 7 i x
  let kept := (actualWidthReturnPaths i).filter fun x => decide (rank x = r)
  change kept.length ≤ 1
  have simple : ∀ i, (actualWidthReturnPaths i).Nodup := by decide
  have keptSimple : kept.Nodup := (List.filter_sublist (l := actualWidthReturnPaths i)).nodup (simple i)
  rw [← List.toFinset_card_of_nodup keptSimple,Finset.card_le_one]
  intro x hx y hy
  obtain ⟨xOn,xRank⟩ := List.mem_filter.mp (List.mem_toFinset.mp hx)
  obtain ⟨yOn,yRank⟩ := List.mem_filter.mp (List.mem_toFinset.mp hy)
  have equal : rank x = rank y := (of_decide_eq_true xRank).trans (of_decide_eq_true yRank).symm
  have increasing {u v} (step : BeforeIn actualWidthReturnPaths i u v) : rank u < rank v := by
    apply copiedReturnCutRank_lt_iff.mpr
    refine ⟨(actualWidthReturnPaths i).idxOf v,?_,step.2.2,le_rfl⟩
    intro a b comparison _ _
    exact actualWidthReturnPaths_copied_steps_have_no_return i a b comparison
  by_contra different
  rcases listBefore_total xOn yOn different with forward | backward
  · exact (increasing forward).ne equal
  · exact (increasing backward).ne equal.symm

/-- With more than one run on a row, the excess is charged separately
to each run. All runs in the fixture fit width one. -/
theorem actualWidthReturnPaths_no_run_excess_at_one :
    copiedReturnRunExcess actualWidthReturnPaths 4 7 1 = 0 := by
  exact sum_eq_zero (fun i _ => sum_eq_zero (fun r _ =>
    Nat.sub_eq_zero_of_le (actualWidthReturnPaths_copied_runs_small i r)))

end OnlineReachabilityPreservers.SourceAudit
