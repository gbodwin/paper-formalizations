import DirectedFlowCutGap.BinaryDrawTreeExecution

/-!
# Retained rounding with charged binary sampling

The sampled controller invokes the binary bound comparison and trial
counter for each finite permutation or cell draw. The bounded charge
combines those modeled binary operations with the controller's declared
word operations and tape materialization.
-/

namespace DirectedFlowCutGap.RetainedBinarySampler

open scoped NNReal
open RetainedGridState FiniteDrawTrees IntegerAdaptiveExecution BinaryDrawTreeExecution

def tape {n L : ℕ} (T : ℕ) (hL : 0 < L) (a : PairFlags n) :
    DrawTree (RetainedTapeInput.Tape L a × ℕ) :=
  BinaryDrawTreeExecution.run T (RetainedDrawTrees.sampleTape hL a)

def tapeBound (n L T : ℕ) : ℕ :=
  (2 * n * n) * oneDrawBound T (RetainedDrawTrees.sampleWidth n L)

theorem tape_cost {n L : ℕ} (T : ℕ) (hL : 0 < L) (a : PairFlags n)
    (r : RetainedTapeInput.Tape L a × ℕ) (hr : r ∈ (ideal (tape T hL a)).support) :
    r.2 ≤ tapeBound n L T :=
  run_cost (RetainedDrawTrees.sampleTape_within hL a) (RetainedDrawTrees.sampleTape_widths hL a) T hr

section Controller

set_option backward.isDefEq.respectTransparency false

variable {n L : ℕ}
variable (adjacency : PairFlags n) (F : CandidateEnumeration.Factory n L)
variable (horder : F.base.enumeration.vertices = List.finRange n) (hL : 0 < L)
variable {demands : Finset (Pair n)}
local notation "inputGraph" => EncodedIntegerShortestPaths.graph adjacency
local notation "witness" => EncodedRoundingState.Witness (demands := demands) adjacency F hL
local notation "Q" => RetainedCandidateSolver.optimizer (demands := demands) adjacency F horder hL
local notation "C" => RetainedGridState.integerCutOracle (G := inputGraph) hL F.base.enumeration

def run (T R restartFuel epochs : ℕ) (s : Code inputGraph demands L) :
    DrawTree (EncodedSampledRounding.ChargedResult witness) :=
  RetainedChargedFairBits.runWith adjacency F horder hL (tape T hL) R restartFuel epochs s

theorem run_projected (T R restartFuel epochs : ℕ) (s : Code inputGraph demands L) :
    map EncodedSampledRounding.ChargedResult.logged (run adjacency F horder hL T R restartFuel epochs s) =
      LazyFairBitTrees.lower T (RetainedDrawTrees.runTree Q hL C R restartFuel epochs s) :=
  RetainedChargedFairBits.runWith_projected adjacency F horder hL T R restartFuel epochs s
    (tape T hL) (fun a => run_value T (RetainedDrawTrees.sampleTape hL a))

theorem initial_cost (T : ℕ) :
    let s := RetainedDemandMask.initial inputGraph F.base.enumeration L hL
    let R := IntegerEpochParameters.restart n
    let fuel := IntegerEpochParameters.fuel n
    ∀ out ∈ (ideal (run adjacency F horder hL T R (fuel + 1) (fuel + 1) s)).support,
      out.operations ≤ EncodedRoundingRuntime.price n L
        (RetainedChargedFairBits.workBound n (fuel + 1) (fuel + 1) fuel) +
          EncodedSampledRounding.epochCharge n (tapeBound n L T) * (fuel + 1) + 1 :=
  RetainedChargedFairBits.initial_runWith_work_bound adjacency F horder hL T
    (tape T hL) (tapeBound n L T) (tape_cost T hL)
    (fun a => run_value T (RetainedDrawTrees.sampleTape hL a))

/-- A polynomial in vertex count and the number of rejection trials.
The hard branch uses only thresholds at most the vertex count. -/
def wordBudget (n T : ℕ) : ℕ :=
  let fuel := n ^ 3 + 2
  let K := (2 * n * n) * oneDrawBound T (n * n + n + 1)
  EncodedRoundingRuntime.price n n (RetainedChargedFairBits.workBound n fuel fuel fuel) +
    EncodedSampledRounding.epochCharge n K * fuel + 1

theorem initial_wordBudget (T : ℕ) (hLn : L ≤ n) :
    let s := RetainedDemandMask.initial inputGraph F.base.enumeration L hL
    let R := IntegerEpochParameters.restart n
    let fuel := IntegerEpochParameters.fuel n
    ∀ out ∈ (ideal (run adjacency F horder hL T R (fuel + 1) (fuel + 1) s)).support,
      out.operations ≤ wordBudget n T := by
  dsimp only
  intro out ho
  have hlog := Nat.log_le_self (IntegerEpochParameters.restart n) (n ^ 3)
  have hf : IntegerEpochParameters.fuel n + 1 ≤ n ^ 3 + 2 := by
    unfold IntegerEpochParameters.fuel
    omega
  have hbase := (Nat.le_succ (IntegerEpochParameters.fuel n)).trans hf
  have hwidth : RetainedDrawTrees.sampleWidth n L ≤ n * n + n + 1 := by
    unfold RetainedDrawTrees.sampleWidth FairBitWords.width
    rw [Nat.log2_eq_log_two]
    have hmax : max (n * n) L ≤ n * n + n := max_le (by omega) (by omega)
    exact Nat.add_le_add_right ((Nat.log_le_self _ _).trans hmax) _
  refine (initial_cost adjacency F horder hL T out ho).trans ?_
  unfold wordBudget EncodedRoundingRuntime.price RetainedChargedFairBits.workBound
    EncodedSampledRounding.epochCharge tapeBound oneDrawBound
    EncodedRoundingState.candidateBound EncodedCandidateOutput.operationBound
  dsimp only
  gcongr

end Controller

end DirectedFlowCutGap.RetainedBinarySampler
