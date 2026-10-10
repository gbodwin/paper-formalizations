import DirectedFlowCutGap.FiniteBinaryPrefix
import DirectedFlowCutGap.BinarySamplerMetadata
import DirectedFlowCutGap.BinaryWeightedSamplingLaw

/-!
# One actual binary callback on a finite fair prefix

The equality observes the actual returned index, rejection flag and counters,
and the actual cumulative failure/trial/consumption/draw ledger fields. It
preserves the real source-state transition. The operation counter is deliberately
excluded from this projection; its pathwise charge theorem is separate.
-/
namespace DirectedFlowCutGap.BinaryTrackedPrefix
open BinaryArithmetic BinarySamplerMetadata BinaryBoundedSampler
open FiniteDrawTrees LazyFairBitTrees MonadicBitSampler

def next : StateM (List (Fin 2)) Bool :=
  (fun i : Fin 2 => decide (i.val=1)) <$> FiniteBinaryPrefix.next

theorem next_index : BinaryRandomWord.bitIndex <$> next = FiniteBinaryPrefix.next := by
  unfold next
  rw [Functor.map_map]
  have h : (BinaryRandomWord.bitIndex ∘ fun i : Fin 2 => decide (i.val=1)) = id := by
    funext i
    fin_cases i <;> rfl
  rw [h,id_map]

structure Metadata where
  failed : Bool
  trials : ℕ
  consumed : ℕ
  draws : ℕ

def metadata (s : Ledger) : Metadata :=
  ⟨s.failed,value s.trials,value s.consumed,value s.draws⟩

def update {n : ℕ} (s : Metadata) (r : BitSamplerCoupling.DefaultOutput n) : Metadata :=
  ⟨s.failed || r.failed,s.trials+r.trials,s.consumed+r.bits,s.draws+1⟩

def view {bound : Bits} (out : Output bound × Ledger) :
    BitSamplerCoupling.DefaultOutput (value bound) × Metadata :=
  (observe out.1,metadata out.2)

theorem record_metadata {bound : Bits} (s : Ledger) (r : Output bound) :
    metadata (record s r) = update (metadata s) (observe r) := by
  simp only [metadata,update,observe,record_failed,record_trials,record_consumed,record_draws]

/-- Whole-monad equality retains the actual source effects while projecting
only the named output/cumulative metadata fields. -/
theorem tracked_refines {M : Type → Type} [Monad M] [LawfulMonad M]
    (bit : M Bool) (bound fuel : Bits) (positive : 0<value bound) (state : Ledger) :
    view <$> ((trackedDraw bit bound positive fuel).run state) =
      (fun r => (r,update (metadata state) r)) <$>
        MonadicBitSampler.draw (BinaryRandomWord.bitIndex <$> bit)
          (value bound) positive (value fuel) := by
  simp only [trackedDraw,StateT.run,Functor.map_map]
  have h : (view ∘ fun r : Output bound => (r,record state r)) =
      (fun r => (r,update (metadata state) r)) ∘ observe := by
    funext r
    exact congrArg (fun s => (observe r,s)) (record_metadata state r)
  rw [h,← Functor.map_map,BinaryBoundedSampler.draw_refines]

/-- A tree only for reasoning about the same callback. It is not eagerly
constructed by the executable binary sampler. -/
def tree (bound fuel : Bits) (positive : 0<value bound) (state : Ledger) :
    FiniteDrawTrees.Tree (BitSamplerCoupling.DefaultOutput (value bound) × Metadata) :=
  FiniteDrawTrees.map (fun r => (r,update (metadata state) r))
    (rejection (value bound) positive (value fuel))

def budget (bound fuel : Bits) : ℕ := value fuel*FairBitWords.width (value bound)

theorem within (bound fuel : Bits) (positive : 0<value bound) (state : Ledger) :
    Within (budget bound fuel) (tree bound fuel positive state) :=
  within_map (rejection_within _ _ _) _

theorem binary (bound fuel : Bits) (positive : 0<value bound) (state : Ledger) :
    Binary (tree bound fuel positive state) := binary_map (rejection_binary _ _ _) _

theorem same_stream (bound fuel : Bits) (positive : 0<value bound) (state : Ledger) :
    view <$> ((trackedDraw next bound positive fuel).run state) =
      FiniteBinaryPrefix.run (tree bound fuel positive state) := by
  rw [tracked_refines,next_index,MonadicBitSampler.draw_refines]
  rw [FiniteBinaryPrefix.run,tree,execute_map]
  rw [map_eq_pure_bind]

theorem actual_suffix (bound fuel : Bits) (positive : 0<value bound)
    (state : Ledger) (xs : List (Fin 2)) (hlen : budget bound fuel≤xs.length) :
    ∃ used≤budget bound fuel,
      ((((trackedDraw next bound positive fuel).run state).run xs).2)=xs.drop used := by
  have he := congrArg (fun p => (p.run xs).2) (same_stream bound fuel positive state)
  have hs := FiniteBinaryPrefix.suffix (within bound fuel positive state)
    (binary bound fuel positive state) xs hlen
  simpa only [← he] using hs

noncomputable section
/-- Independent finite input bits realize the same actual callback's observed
output and cumulative physical counters as fresh fair requests. -/
theorem output_law (bound fuel : Bits) (positive : 0<value bound) (state : Ledger) :
    (FiniteBinaryPrefix.prefixLaw (budget bound fuel)).map (fun xs =>
      view ((((trackedDraw next bound positive fuel).run state).run xs).1)) =
      (((trackedDraw BinaryWeightedSamplingLaw.fairBit bound positive fuel).run state).map view) := by
  have hs := same_stream bound fuel positive state
  have he : (fun xs => view ((((trackedDraw next bound positive fuel).run state).run xs).1)) =
      (fun xs => ((FiniteBinaryPrefix.run (tree bound fuel positive state)).run xs).1) := by
    funext xs
    exact congrArg (fun p => (p.run xs).1) hs
  rw [he,FiniteBinaryPrefix.output_law (within bound fuel positive state)
    (binary bound fuel positive state)]
  change _ = view <$> ((trackedDraw BinaryWeightedSamplingLaw.fairBit bound positive fuel).run state)
  rw [tracked_refines,BinaryWeightedSamplingLaw.fairBit_index,MonadicBitSampler.draw_refines,
    BinaryWeightedSamplingLaw.execute_binary_ideal (rejection_binary _ _ _)]
  exact law_map _ _ _

end
end DirectedFlowCutGap.BinaryTrackedPrefix
