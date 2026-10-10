import DirectedFlowCutGap.BinaryFullPrefix

/-! Pathwise declared instruction charge for the same complete binary record
returned from an actual finite bit list. This is one sampler callback, not a
host-runtime or whole-query complexity theorem. -/
namespace DirectedFlowCutGap.BinaryFullPrefixCost
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinaryBoundedSampler BinarySamplerMetadata
open FiniteDrawTrees LazyFairBitTrees MonadicBitSampler
noncomputable section

theorem run_supported {A : Type} {p : FiniteDrawTrees.Tree A} (hp : Binary p) (xs : List (Fin 2)) :
    ((FiniteBinaryPrefix.run p).run xs).1 ∈ (ideal p).support := by
  induction hp generalizing xs with
  | pure a => exact PMF.mem_support_pure_iff _ _ |>.mpr rfl
  | @draw p hp ih =>
    cases xs with
    | nil =>
      change ((FiniteBinaryPrefix.run (p 0)).run []).1 ∈
        ((uniformDraw 2 (by decide)).bind (fun b => ideal (p b))).support
      apply (PMF.mem_support_bind_iff _ _ _).mpr
      exact ⟨0,PMF.mem_support_uniformOfFintype _,ih 0 []⟩
    | cons b bs =>
      rw [FiniteBinaryPrefix.run_cons]
      apply (PMF.mem_support_bind_iff _ _ _).mpr
      exact ⟨b,PMF.mem_support_uniformOfFintype _,ih b bs⟩

theorem actual_supported (bound fuel : Bits) (positive : 0<value bound)
    (state : Ledger) (xs : List (Fin 2)) :
    (((trackedDraw BinaryTrackedPrefix.next bound positive fuel).run state).run xs).1 ∈
      ((trackedDraw BinaryWeightedSamplingLaw.fairBit bound positive fuel).run state).support := by
  have he : (trackedDraw BinaryWeightedSamplingLaw.fairBit bound positive fuel).run state =
      execute (liftBit (PMF.uniformOfFintype (Fin 2))) (BinaryFullPrefix.tree bound fuel positive state) := by
    simpa only [BinaryWeightedSamplingLaw.fairBit,PMF.monad_map_eq_map] using
      (BinaryFullPrefix.execute_tree (PMF.uniformOfFintype (Fin 2)) bound fuel positive state).symm
  rw [BinaryFullPrefix.same_stream,he,
    BinaryWeightedSamplingLaw.execute_binary_ideal (BinaryFullPrefix.binary bound fuel positive state)]
  exact run_supported (BinaryFullPrefix.binary bound fuel positive state) xs

/-- Same finite execution and full returned ledger; no output resampling or
projection is used to obtain the declared charge bound. -/
theorem actual_charge (bound fuel : Bits) (positive : 0<value bound)
    (state : Ledger) (xs : List (Fin 2)) :
    ((((trackedDraw BinaryTrackedPrefix.next bound positive fuel).run state).run xs).1).2.operations ≤
      state.operations+updateBound state bound fuel :=
  trackedDraw_charge BinaryWeightedSamplingLaw.fairBit bound fuel positive state
    (actual_supported bound fuel positive state xs)

end
end DirectedFlowCutGap.BinaryFullPrefixCost
