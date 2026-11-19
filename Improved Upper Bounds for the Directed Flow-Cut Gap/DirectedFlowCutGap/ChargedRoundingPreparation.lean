import DirectedFlowCutGap.EncodedEpochParameters
import DirectedFlowCutGap.EncodedRoundingState

/-!
# Prepared integer inputs with charged initial mass

Build the retained candidate dictionary and original threshold mask.
Compute the all-ones starting state's mass using the existing counted
array scan. The accepted state carries the original proof indices and
has the exact data of the ordinary integer rounder's initial state.
-/

namespace DirectedFlowCutGap.ChargedRoundingPreparation

open scoped NNReal
open RetainedGridState
open EncodedIntegerShortestPaths (graph)

private def arrayCharge (n : ℕ) : ℕ := (n*n+n+1)*(2*n+2)+2*n+12

def initialState {n L : ℕ} (adjacency : PairFlags n) (hL : 0 < L) (mask : PairFlags n)
    (hmask : remainingSet mask =
      CandidateSchedule.unweightedDemands (graph adjacency) (L : ℝ≥0)) :
    Code (graph adjacency) (remainingSet mask) L × ℕ :=
  let cut : Flags n := Vector.replicate n false
  let weights : Family n := Vector.replicate n (Vector.replicate n (Vector.replicate n 1))
  let m := EncodedRoundingState.mass mask cut weights
  let data : Data n := ⟨mask, cut, weights, 1, m.1⟩
  let hlevel : 1 ≤ (L : ℝ≥0) := by exact_mod_cast Nat.succ_le_of_lt hL
  let base := initialMaskedCode (graph adjacency) hlevel mask hmask
  have hd : data = base.data := by
    change Data.mk mask cut weights 1 m.1 = Data.mk mask cut weights 1 (massNumerator mask cut weights)
    rw [show m.1 = massNumerator mask cut weights from EncodedRoundingState.mass_value mask cut weights]
  (⟨data, hd.symm ▸ base.valid⟩, m.2 + arrayCharge n)

theorem initialState_data {n L : ℕ} (adjacency : PairFlags n) (hL : 0 < L) (mask : PairFlags n)
    (hmask : remainingSet mask =
      CandidateSchedule.unweightedDemands (graph adjacency) (L : ℝ≥0)) :
    (initialState adjacency hL mask hmask).1.data =
      (initialMaskedCode (graph adjacency) (by exact_mod_cast Nat.succ_le_of_lt hL) mask hmask).data := by
  unfold initialState
  dsimp only
  rw [EncodedRoundingState.mass_value]
  rfl

theorem initialState_charge {n L : ℕ} (adjacency : PairFlags n) (hL : 0 < L) (mask : PairFlags n)
    (hmask : remainingSet mask =
      CandidateSchedule.unweightedDemands (graph adjacency) (L : ℝ≥0)) :
    (initialState adjacency hL mask hmask).2 ≤ EncodedRoundingState.massBound n + arrayCharge n :=
  Nat.add_le_add_right (EncodedRoundingState.mass_bound mask _ _) _

structure Prepared {n : ℕ} (adjacency : PairFlags n) (L : ℕ) where
  parameters : EncodedEpochParameters.Parameters
  factory : CandidateEnumeration.Factory n L
  mask : PairFlags n
  state : Code (graph adjacency) (remainingSet mask) L
  charge : ℕ

def prepare {n : ℕ} (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) : Prepared adjacency L :=
  let params := EncodedEpochParameters.compute n
  let factory := CandidateEnumeration.make n L
  let mask := EncodedRoundingInput.demandMask factory.base.enumeration adjacency L
  let start := initialState adjacency hL mask.1
    (EncodedRoundingInput.demandMask_correct factory.base.enumeration adjacency L)
  ⟨params, factory, mask.1, start.1, params.work + factory.work + mask.2 + start.2 + 7⟩

theorem prepare_value {n : ℕ} (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) :
    let F := CandidateEnumeration.make n L
    let p := prepare adjacency L hL
    p.parameters.restart = IntegerEpochParameters.restart n ∧
    p.parameters.fuel = IntegerEpochParameters.fuel n ∧
    p.parameters.cap = IntegerEpochParameters.cap n ∧
    p.factory = F ∧ p.mask = RetainedDemandMask.compute (graph adjacency) F.base.enumeration L ∧
    p.state.data = (RetainedDemandMask.initial (graph adjacency) F.base.enumeration L hL).data := by
  let F := CandidateEnumeration.make n L
  let mask := EncodedRoundingInput.demandMask F.base.enumeration adjacency L
  have h := EncodedRoundingInput.demandMask_value F.base.enumeration adjacency L
  refine ⟨EncodedEpochParameters.compute_restart n, EncodedEpochParameters.compute_fuel n,
    EncodedEpochParameters.compute_cap n, rfl, h, ?_⟩
  change (initialState adjacency hL mask.1
      (EncodedRoundingInput.demandMask_correct F.base.enumeration adjacency L)).1.data =
    (RetainedDemandMask.initial (graph adjacency) F.base.enumeration L hL).data
  rw [initialState_data]
  change Data.mk mask.1 _ _ _ _ = Data.mk (RetainedDemandMask.compute (graph adjacency)
    F.base.enumeration L) _ _ _ _
  rw [show mask.1 = _ from h]

def budget (n : ℕ) : ℕ :=
  EncodedEpochParameters.operationBound n + (120*n*(n+1)+161*n+127) +
    EncodedRoundingInput.maskBound n + EncodedRoundingState.massBound n + arrayCharge n + 7

theorem budget_mono {u v : ℕ} (h : u ≤ v) : budget u ≤ budget v := by
  unfold budget EncodedEpochParameters.operationBound EncodedRoundingInput.maskBound
    EncodedRoundingState.massBound EncodedRoundingState.sumOverhead arrayCharge
    EncodedIntegerShortestPaths.distanceBound EncodedRoundingInput.arrayBound
  gcongr

theorem prepare_charge {n : ℕ} (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) (hLn : L ≤ n) :
    (prepare adjacency L hL).charge ≤ budget n := by
  let F := CandidateEnumeration.make n L
  let mask := EncodedRoundingInput.demandMask F.base.enumeration adjacency L
  have hparams := EncodedEpochParameters.compute_bound n
  have hf : F.work ≤ 120*n*(n+1)+161*n+127 := by
    have hw := CandidateEnumeration.make_work n L
    have ha := Nat.mul_le_mul_left (120*n) (Nat.add_le_add_right hLn 1)
    change F.work = _ at hw
    rw [hw]
    omega
  have hm := EncodedRoundingInput.demandMask_bound F.base.enumeration adjacency L
  have hi := initialState_charge adjacency hL mask.1
    (EncodedRoundingInput.demandMask_correct F.base.enumeration adjacency L)
  change (EncodedEpochParameters.compute n).work + F.work +
    (EncodedRoundingInput.demandMask F.base.enumeration adjacency L).2 +
    (initialState adjacency hL mask.1 _).2 + 7 ≤ _
  unfold budget
  omega

end DirectedFlowCutGap.ChargedRoundingPreparation
