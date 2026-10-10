import DirectedFlowCutGap.BinarySamplerTrees
import DirectedFlowCutGap.BinaryWeightedSampling

/-! The final original-weight ticket draw uses the same finite bit reader as
its caller. These interpreter equalities preserve all labels and charge fields;
no selected-label projection or fresh random stream is introduced. -/
namespace DirectedFlowCutGap.BinaryTicketTrees
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinaryWeightedSampling FiniteDrawTrees LazyFairBitTrees

section Execute
variable {M : Type → Type} [Monad M] [LawfulMonad M]
variable (sample : (n : ℕ) → 0<n → M (Fin n))

private theorem map_execute {A B : Type} (f : A → B) (p : FiniteDrawTrees.Tree A) :
    execute sample (f <$> p)=f <$> execute sample p := by
  change execute sample (FiniteDrawTrees.map f p)=_
  simpa only [bind_pure_comp] using MonadicBitSampler.execute_map sample f p

theorem checked_execute (bound fuel : Bits) :
    execute sample (BinaryBoundedSampler.checkedDrawCharged BinarySamplerTrees.bit bound fuel)=
      BinaryBoundedSampler.checkedDrawCharged (execute sample BinarySamplerTrees.bit) bound fuel := by
  unfold BinaryBoundedSampler.checkedDrawCharged
  dsimp only []
  split_ifs
  · rfl
  · change execute sample (FiniteDrawTrees.bind _ _)=_
    rw [MonadicBitSampler.execute_bind,BinarySamplerTrees.draw_execute]
    rfl

theorem prepared_execute (p : Prepared) (fuel : Bits) :
    execute sample (samplePrepared BinarySamplerTrees.bit p fuel)=
      samplePrepared (execute sample BinarySamplerTrees.bit) p fuel := by
  unfold samplePrepared
  rw [map_execute,checked_execute]

theorem sample_execute (xs : BinaryWeightedMasses.Input) (fuel : Bits) :
    execute sample (BinaryWeightedSampling.sample BinarySamplerTrees.bit xs fuel)=
      BinaryWeightedSampling.sample (execute sample BinarySamplerTrees.bit) xs fuel := by
  unfold BinaryWeightedSampling.sample
  rw [map_execute,prepared_execute]

theorem events_execute {n : ℕ} (events : List (BinaryFractionalCore.Event n)) (fuel : Bits) :
    execute sample (sampleEvents BinarySamplerTrees.bit events fuel)=
      sampleEvents (execute sample BinarySamplerTrees.bit) events fuel := by
  unfold sampleEvents
  rw [map_execute,sample_execute]
end Execute

theorem checked_binary (bound fuel : Bits) :
    Binary (BinaryBoundedSampler.checkedDrawCharged BinarySamplerTrees.bit bound fuel) := by
  unfold BinaryBoundedSampler.checkedDrawCharged
  dsimp only []
  split_ifs
  · exact .pure _
  · exact binary_bind (BinarySamplerTrees.draw_binary _ _ _) _ (fun _ => .pure _)

theorem checked_within (bound fuel : Bits) :
    Within (value fuel*FairBitWords.width (value bound))
      (BinaryBoundedSampler.checkedDrawCharged BinarySamplerTrees.bit bound fuel) := by
  unfold BinaryBoundedSampler.checkedDrawCharged
  dsimp only []
  split_ifs
  · exact .pure _ _
  · exact within_bind (BinarySamplerTrees.draw_within _ _ _) _ (r := 0) (fun _ => .pure 0 _)

theorem events_binary {n : ℕ} (events : List (BinaryFractionalCore.Event n)) (fuel : Bits) :
    Binary (sampleEvents BinarySamplerTrees.bit events fuel) := by
  exact binary_map (binary_map (binary_map (checked_binary _ _) _) _) _

theorem events_within {n : ℕ} (events : List (BinaryFractionalCore.Event n)) (fuel : Bits) :
    Within (value fuel*FairBitWords.width (value (prepare (eventInput events).1).total))
      (sampleEvents BinarySamplerTrees.bit events fuel) := by
  exact within_map (within_map (within_map (checked_within _ _) _) _) _

end DirectedFlowCutGap.BinaryTicketTrees
