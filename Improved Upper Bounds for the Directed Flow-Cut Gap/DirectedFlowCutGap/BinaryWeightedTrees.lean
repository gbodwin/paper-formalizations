import DirectedFlowCutGap.BinaryRepeatedPrefix
import DirectedFlowCutGap.StatefulHeavyQuery

/-! Whole-record interpretation through the actual retained weighted
reduction. The prefix budget uses the transformed dimension actually prepared
by this input. This is a finite-source law, not a cost for preparing that
budget or a physical implementation of raw rational materialization. -/
namespace DirectedFlowCutGap.BinaryWeightedTrees
noncomputable section
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinarySamplerMetadata BinaryRetainedTape
open FiniteDrawTrees LazyFairBitTrees MonadicBitSampler
open EncodedUnitCostReplication EncodedWeightedVertexQuery

def sample {M : Type → Type} [Monad M] (bit : M Bool) : TapeSampler (StateT Ledger M) :=
  fun N L hL => callback bit (StatefulBoundedRoundingQuality.canonicalFuel N)
    L.bits (value_bits L) hL

def readyBudget {n : ℕ} {D : Input n} (r : Ready D) (extra : ℕ) : ℕ :=
  (extra+1)*BinaryEntryTrees.budget r.chain.size
    (StatefulBoundedRoundingQuality.canonicalFuel r.chain.size) r.chain.cutoff.bits

def budget {n : ℕ} (D : Input n) (extra : ℕ) : ℕ :=
  match prepare D with
  | .inl _ => 0
  | .inr r => readyBudget r extra

section Execute
variable {M : Type → Type} [Monad M] [LawfulMonad M] (b : M (Fin 2))

theorem ready_execute {n : ℕ} {D : Input n} (r : Ready D) (extra : ℕ) (state : Ledger) :
    FiniteDrawTrees.execute (liftBit b)
      ((runReady (sample BinarySamplerTrees.bit) r extra).run state) =
      ((runReady (sample (BinaryTapeTrees.boolBit b)) r extra).run state) := by
  unfold runReady
  apply StatefulTreeInterpreter.bind_execute b _ _ _ _
    (fun s => BinaryRepeatedPrefix.execute _ _ _ _ _ b extra s)
  intro core s
  rfl

theorem run_execute {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger) :
    FiniteDrawTrees.execute (liftBit b)
      ((EncodedWeightedVertexQuery.run (sample BinarySamplerTrees.bit) D extra).run state) =
      ((EncodedWeightedVertexQuery.run (sample (BinaryTapeTrees.boolBit b)) D extra).run state) := by
  unfold EncodedWeightedVertexQuery.run
  cases h : prepare D with
  | inl done => rfl
  | inr r => exact ready_execute b r extra state
end Execute

theorem ready_binary {n : ℕ} {D : Input n} (r : Ready D) (extra : ℕ) (state : Ledger) :
    Binary ((runReady (sample BinarySamplerTrees.bit) r extra).run state) := by
  unfold runReady
  apply StatefulTreeInterpreter.binary_bind _ _
    (fun s => BinaryRepeatedPrefix.binary _ _ _ _ _ extra s)
  intro core s
  exact .pure _

theorem ready_within {n : ℕ} {D : Input n} (r : Ready D) (extra : ℕ) (state : Ledger) :
    Within (readyBudget r extra) ((runReady (sample BinarySamplerTrees.bit) r extra).run state) := by
  unfold runReady readyBudget
  apply StatefulTreeInterpreter.within_bind _ _ (r := 0)
    (fun s => BinaryRepeatedPrefix.within _ _ _ _ _ extra s)
  intro core s
  exact .pure _ _

theorem run_binary {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger) :
    Binary ((EncodedWeightedVertexQuery.run (sample BinarySamplerTrees.bit) D extra).run state) := by
  unfold EncodedWeightedVertexQuery.run
  cases h : prepare D with
  | inl done => exact .pure _
  | inr r => exact ready_binary r extra state

theorem run_within {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger) :
    Within (budget D extra)
      ((EncodedWeightedVertexQuery.run (sample BinarySamplerTrees.bit) D extra).run state) := by
  unfold EncodedWeightedVertexQuery.run budget
  cases h : prepare D with
  | inl done => exact .pure _ _
  | inr r => exact ready_within r extra state

end
end DirectedFlowCutGap.BinaryWeightedTrees
