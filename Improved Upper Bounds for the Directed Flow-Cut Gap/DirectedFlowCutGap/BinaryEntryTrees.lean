import DirectedFlowCutGap.BinaryControllerPrefix
import DirectedFlowCutGap.EncodedAllRegimeRounding

/-! Full-state interpretation of the charged entry and its actual guards.
All output fields and the same physical ledger are retained. The fixed prefix
budget includes every possible epoch, including early-stop histories. -/
namespace DirectedFlowCutGap.BinaryEntryTrees
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinarySamplerMetadata BinaryRetainedTape
open FiniteDrawTrees LazyFairBitTrees MonadicBitSampler RetainedGridState
variable {n L : ℕ} (fuel cutoff : Bits) (hcut : value cutoff=L)
  (adjacency : PairFlags n) (hL : 0<L)

def budget (n : ℕ) (fuel cutoff : Bits) : ℕ :=
  ((EncodedEpochParameters.compute n).fuel+1)*BinaryControllerTrees.callBudget n fuel cutoff

section Execute
variable {M : Type → Type} [Monad M] [LawfulMonad M] (b : M (Fin 2))

theorem entry_execute (state : Ledger) :
    FiniteDrawTrees.execute (liftBit b)
      ((EncodedRoundingEntry.run (callback BinarySamplerTrees.bit fuel cutoff hcut hL)
        adjacency hL).run state) =
      ((EncodedRoundingEntry.run (callback (BinaryTapeTrees.boolBit b) fuel cutoff hcut hL)
        adjacency hL).run state) := by
  unfold EncodedRoundingEntry.run
  exact StatefulTreeInterpreter.map_execute b _ _ _
    (fun s => BinaryControllerTrees.run_execute adjacency _ _ hL b fuel cutoff hcut _ _ _ _ s) state

theorem all_execute (state : Ledger) :
    FiniteDrawTrees.execute (liftBit b)
      ((EncodedAllRegimeRounding.run (callback BinarySamplerTrees.bit fuel cutoff hcut hL)
        adjacency hL).run state) =
      ((EncodedAllRegimeRounding.run (callback (BinaryTapeTrees.boolBit b) fuel cutoff hcut hL)
        adjacency hL).run state) := by
  unfold EncodedAllRegimeRounding.run
  dsimp only []
  split_ifs
  · rfl
  · exact StatefulTreeInterpreter.map_execute b _ _ _
      (fun s => entry_execute fuel cutoff hcut adjacency hL b s) state
  · rfl
  · rfl
end Execute

theorem entry_binary (state : Ledger) :
    Binary ((EncodedRoundingEntry.run (callback BinarySamplerTrees.bit fuel cutoff hcut hL)
      adjacency hL).run state) := by
  unfold EncodedRoundingEntry.run
  exact StatefulTreeInterpreter.binary_map _ _
    (fun s => BinaryControllerTrees.run_binary adjacency _ _ hL fuel cutoff hcut _ _ _ _ s) state

theorem entry_within (state : Ledger) :
    Within (budget n fuel cutoff)
      ((EncodedRoundingEntry.run (callback BinarySamplerTrees.bit fuel cutoff hcut hL)
        adjacency hL).run state) := by
  unfold EncodedRoundingEntry.run budget
  exact StatefulTreeInterpreter.within_map _ _
    (fun s => BinaryControllerTrees.run_within adjacency _ _ hL fuel cutoff hcut _ _ _ _ s) state

theorem all_binary (state : Ledger) :
    Binary ((EncodedAllRegimeRounding.run (callback BinarySamplerTrees.bit fuel cutoff hcut hL)
      adjacency hL).run state) := by
  unfold EncodedAllRegimeRounding.run
  dsimp only []
  split_ifs
  · exact .pure _
  · exact StatefulTreeInterpreter.binary_map _ _
      (fun s => entry_binary fuel cutoff hcut adjacency hL s) state
  · exact .pure _
  · exact .pure _

theorem all_within (state : Ledger) :
    Within (budget n fuel cutoff)
      ((EncodedAllRegimeRounding.run (callback BinarySamplerTrees.bit fuel cutoff hcut hL)
        adjacency hL).run state) := by
  unfold EncodedAllRegimeRounding.run
  dsimp only []
  split_ifs
  · exact .pure _ _
  · exact StatefulTreeInterpreter.within_map _ _
      (fun s => entry_within fuel cutoff hcut adjacency hL s) state
  · exact .pure _ _
  · exact .pure _ _

end DirectedFlowCutGap.BinaryEntryTrees
