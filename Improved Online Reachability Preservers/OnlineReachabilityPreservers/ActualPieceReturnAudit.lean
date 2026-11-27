import Mathlib.Data.Fin.VecNotation
import OnlineReachabilityPreservers.ComponentSplitCleaning

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

end OnlineReachabilityPreservers.SourceAudit
