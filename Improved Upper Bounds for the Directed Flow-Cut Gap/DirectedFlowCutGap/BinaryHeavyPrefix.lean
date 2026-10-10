import DirectedFlowCutGap.BinaryWeightedTrees

/-! The same actual heavy preparation and retained weighted query interpreted
with a finite input stream. Complete output/ledger law is retained. Raw-input
materialization, prefix-budget construction and physical storage/runtime remain
separate; this does not yet lower the outer adaptive packing controller. -/
namespace DirectedFlowCutGap.BinaryHeavyPrefix
noncomputable section
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinarySamplerMetadata
open FiniteDrawTrees LazyFairBitTrees MonadicBitSampler EncodedUnitCostReplication

/-- Generic-bit execution has exactly the existing heavy-query body. -/
def run {M : Type → Type} [Monad M] (bit : M Bool) {n : ℕ} (D : Input n) (extra : ℕ) :
    StateT Ledger M (EncodedWeightedVertexQuery.Output n) := do
  let prepared := EncodedHeavyVertexPreparation.prepare D
  if prepared.1.size=0 then
    pure (StatefulHeavyQuery.finish prepared (StatefulHeavyQuery.emptyOutput prepared.1.size))
  else
    let inner ← EncodedWeightedVertexQuery.run (BinaryWeightedTrees.sample bit) prepared.1.data extra
    pure (StatefulHeavyQuery.finish prepared inner)

theorem fair_eq {n : ℕ} (D : Input n) (extra : ℕ) :
    run BinaryWeightedSamplingLaw.fairBit D extra=StatefulHeavyQuery.run D extra := rfl

def budget {n : ℕ} (D : Input n) (extra : ℕ) : ℕ :=
  if (StatefulHeavyQuery.residual D).size=0 then 0 else
    BinaryWeightedTrees.budget (StatefulHeavyQuery.residual D).data extra

abbrev tree {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger) :=
  (run BinarySamplerTrees.bit D extra).run state

theorem execute {M : Type → Type} [Monad M] [LawfulMonad M] (b : M (Fin 2))
    {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger) :
    FiniteDrawTrees.execute (liftBit b) (tree D extra state)=
      (run (BinaryTapeTrees.boolBit b) D extra).run state := by
  unfold tree run
  dsimp only []
  split_ifs
  · rfl
  · apply StatefulTreeInterpreter.bind_execute b _ _ _ _
      (fun s => BinaryWeightedTrees.run_execute b _ extra s)
    intro inner s
    rfl

theorem binary {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger) :
    Binary (tree D extra state) := by
  unfold tree run
  dsimp only []
  split_ifs
  · exact .pure _
  · apply StatefulTreeInterpreter.binary_bind _ _
      (fun s => BinaryWeightedTrees.run_binary _ extra s)
    intro inner s
    exact .pure _

theorem within {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger) :
    Within (budget D extra) (tree D extra state) := by
  unfold tree run budget StatefulHeavyQuery.residual
  dsimp only []
  split_ifs
  · exact .pure _ _
  · apply StatefulTreeInterpreter.within_bind _ _ (r := 0)
      (fun s => BinaryWeightedTrees.run_within _ extra s)
    intro inner s
    exact .pure _ _

theorem same_stream {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger) :
    (run BinaryTrackedPrefix.next D extra).run state=FiniteBinaryPrefix.run (tree D extra state) :=
  (execute FiniteBinaryPrefix.next D extra state).symm

/-- A sufficiently long actual input list is consumed at most up to the
proved adaptive budget, with its literal remaining suffix returned. -/
theorem suffix {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger)
    (xs : List (Fin 2)) (hlen : budget D extra≤xs.length) :
    ∃ used≤budget D extra,
      (((run BinaryTrackedPrefix.next D extra).run state).run xs).2=xs.drop used := by
  rw [same_stream]
  exact FiniteBinaryPrefix.suffix (within D extra state) (binary D extra state) xs hlen

private theorem fair_law {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger) :
    ideal (tree D extra state)=(StatefulHeavyQuery.run D extra).run state := by
  rw [← fair_eq D extra,← BinaryWeightedSamplingLaw.execute_binary_ideal (binary D extra state)]
  simpa only [BinaryTapeTrees.boolBit,BinaryWeightedSamplingLaw.fairBit,PMF.monad_map_eq_map] using
    execute (PMF.uniformOfFintype (Fin 2)) D extra state

theorem output_law {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger) :
    (FiniteBinaryPrefix.prefixLaw (budget D extra)).map
      (fun xs => (((run BinaryTrackedPrefix.next D extra).run state).run xs).1)=
      (StatefulHeavyQuery.run D extra).run state := by
  rw [same_stream,FiniteBinaryPrefix.output_law (within D extra state) (binary D extra state)]
  exact fair_law D extra state

theorem actual_supported {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger) (xs : List (Fin 2)) :
    (((run BinaryTrackedPrefix.next D extra).run state).run xs).1 ∈
      ((StatefulHeavyQuery.run D extra).run state).support := by
  rw [same_stream,← fair_law]
  exact BinaryFullPrefixCost.run_supported (binary D extra state) xs

end
end DirectedFlowCutGap.BinaryHeavyPrefix
