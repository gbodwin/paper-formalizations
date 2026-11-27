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

theorem actualWidthReturnPaths_old_fails :
    ¬ NoShortReturnAcrossWidthCuts actualWidthReturnPaths 4 7 := by
  intro safe
  have forward : BeforeIn actualWidthReturnPaths 0 0 5 := by decide
  have different : (actualWidthReturnPaths 0).idxOf 0/4 ≠ (actualWidthReturnPaths 0).idxOf 5/4 := by decide
  have returnEdge : Edge (pathPrecedenceGraph actualWidthReturnPaths) 5 0 := by
    simp only [Edge,pathPrecedenceGraph,mem_filter,mem_univ,true_and]
    exact ⟨5,by decide⟩
  have path : (5 : Fin 12) ∈ reachIn (pathPrecedenceGraph actualWidthReturnPaths) 0 4 :=
    reachIn_succ.mpr (Or.inr ⟨0,returnEdge,target_mem_reachIn _ _ 3⟩)
  exact safe forward different path

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

end OnlineReachabilityPreservers.SourceAudit
