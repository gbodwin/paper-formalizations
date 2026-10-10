import DirectedFlowCutGap.StatefulTreeInterpreter
import DirectedFlowCutGap.EncodedSampledRounding

/-! Full-record interpretation and a fixed independent-bit prefix budget for
the actual adaptive graph controller. Bounds depend on the supplied number of
epochs; no cost/quality/physical-memory assertion is added. -/
namespace DirectedFlowCutGap.BinaryControllerTrees
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinarySamplerMetadata BinaryRetainedTape
open FiniteDrawTrees LazyFairBitTrees MonadicBitSampler
open RetainedGridState IntegerAdaptiveExecution EncodedIntegerShortestPaths EncodedRoundingState

private theorem width_mono {a b : ℕ} (h : a≤b) : FairBitWords.width a≤FairBitWords.width b := by
  apply Nat.add_le_add_right
  by_cases hz : a=0
  · simp [hz]
  · exact (Nat.le_log2 (by omega : b≠0)).2 ((Nat.log2_self_le hz).trans h)

def callBudget (n : ℕ) (fuel cutoff : Bits) : ℕ := BinaryTapeBudget.budget (n*n) fuel cutoff

theorem callback_within (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) (a : PairFlags n) (s : Ledger) :
    Within (callBudget n fuel cutoff) ((callback BinarySamplerTrees.bit fuel cutoff hcut hL a).run s) := by
  apply within_mono (BinaryTapeBudget.callback_within fuel cutoff hcut hL a s)
  have hm : (RetainedTapeInput.activeList a).length≤n*n := by
    rw [RetainedTapeInput.activeList_length]
    exact RetainedDrawTrees.active_card_le a
  have hw := width_mono hm
  unfold callBudget BinaryTapeBudget.budget
  exact Nat.mul_le_mul (Nat.mul_le_mul_right (value fuel) hm)
    (Nat.add_le_add_right hw _)

section Controller
variable {n L : ℕ} (adjacency : PairFlags n) (F : CandidateEnumeration.Factory n L)
variable (horder : F.base.enumeration.vertices=List.finRange n) (hL : 0<L)
variable {demands : Finset (Pair n)}
local notation "H" => EncodedRoundingState.Witness (demands := demands) adjacency F hL

section Execute
variable {M : Type → Type} [Monad M] [LawfulMonad M] (b : M (Fin 2))

theorem execute (fuel cutoff : Bits) (hcut : value cutoff=L)
    (R restartFuel epochs : ℕ) (c : Cache H) (state : Ledger) :
    FiniteDrawTrees.execute (liftBit b)
      ((EncodedSampledRounding.executeSampled adjacency F horder hL
        (callback BinarySamplerTrees.bit fuel cutoff hcut hL) R restartFuel epochs c).run state) =
      ((EncodedSampledRounding.executeSampled adjacency F horder hL
        (callback (BinaryTapeTrees.boolBit b) fuel cutoff hcut hL) R restartFuel epochs c).run state) := by
  induction epochs generalizing c state with
  | zero => rfl
  | succ epochs ih =>
    simp only [EncodedSampledRounding.executeSampled]
    split_ifs
    · rfl
    · apply StatefulTreeInterpreter.bind_execute b
      · intro s
        exact BinaryTapeTrees.callback_execute b fuel cutoff hcut hL _ s
      · intro t s
        exact StatefulTreeInterpreter.map_execute b _ _ _ (fun s => ih _ s) s

theorem run_execute (fuel cutoff : Bits) (hcut : value cutoff=L)
    (R restartFuel epochs : ℕ) (st : Code (graph adjacency) demands L) (state : Ledger) :
    FiniteDrawTrees.execute (liftBit b)
      ((EncodedSampledRounding.runSampled adjacency F horder hL
        (callback BinarySamplerTrees.bit fuel cutoff hcut hL) R restartFuel epochs st).run state) =
      ((EncodedSampledRounding.runSampled adjacency F horder hL
        (callback (BinaryTapeTrees.boolBit b) fuel cutoff hcut hL) R restartFuel epochs st).run state) := by
  unfold EncodedSampledRounding.runSampled
  exact StatefulTreeInterpreter.map_execute b _ _ _
    (fun s => execute adjacency F horder hL b fuel cutoff hcut R restartFuel epochs _ s) state

end Execute

theorem execute_binary (fuel cutoff : Bits) (hcut : value cutoff=L)
    (R restartFuel epochs : ℕ) (c : Cache H) (state : Ledger) :
    Binary ((EncodedSampledRounding.executeSampled adjacency F horder hL
      (callback BinarySamplerTrees.bit fuel cutoff hcut hL) R restartFuel epochs c).run state) := by
  induction epochs generalizing c state with
  | zero => exact .pure _
  | succ epochs ih =>
    simp only [EncodedSampledRounding.executeSampled]
    split_ifs
    · exact .pure _
    · apply StatefulTreeInterpreter.binary_bind
      · intro s
        exact BinaryTapeBudget.callback_binary fuel cutoff hcut hL _ s
      · intro t s
        exact StatefulTreeInterpreter.binary_map _ _ (fun s => ih _ s) s

theorem execute_within (fuel cutoff : Bits) (hcut : value cutoff=L)
    (R restartFuel epochs : ℕ) (c : Cache H) (state : Ledger) :
    Within (epochs*callBudget n fuel cutoff)
      ((EncodedSampledRounding.executeSampled adjacency F horder hL
        (callback BinarySamplerTrees.bit fuel cutoff hcut hL) R restartFuel epochs c).run state) := by
  induction epochs generalizing c state with
  | zero => exact .pure _ _
  | succ epochs ih =>
    simp only [EncodedSampledRounding.executeSampled]
    split_ifs
    · exact .pure _ _
    · rw [Nat.succ_mul,Nat.add_comm]
      apply StatefulTreeInterpreter.within_bind
      · intro s
        exact callback_within fuel cutoff hcut hL _ s
      · intro t s
        exact StatefulTreeInterpreter.within_map _ _ (fun s => ih _ s) s

theorem run_binary (fuel cutoff : Bits) (hcut : value cutoff=L)
    (R restartFuel epochs : ℕ) (st : Code (graph adjacency) demands L) (state : Ledger) :
    Binary ((EncodedSampledRounding.runSampled adjacency F horder hL
      (callback BinarySamplerTrees.bit fuel cutoff hcut hL) R restartFuel epochs st).run state) := by
  unfold EncodedSampledRounding.runSampled
  exact StatefulTreeInterpreter.binary_map _ _
    (fun s => execute_binary adjacency F horder hL fuel cutoff hcut R restartFuel epochs _ s) state

theorem run_within (fuel cutoff : Bits) (hcut : value cutoff=L)
    (R restartFuel epochs : ℕ) (st : Code (graph adjacency) demands L) (state : Ledger) :
    Within (epochs*callBudget n fuel cutoff)
      ((EncodedSampledRounding.runSampled adjacency F horder hL
        (callback BinarySamplerTrees.bit fuel cutoff hcut hL) R restartFuel epochs st).run state) := by
  unfold EncodedSampledRounding.runSampled
  exact StatefulTreeInterpreter.within_map _ _
    (fun s => execute_within adjacency F horder hL fuel cutoff hcut R restartFuel epochs _ s) state

end Controller
end DirectedFlowCutGap.BinaryControllerTrees
