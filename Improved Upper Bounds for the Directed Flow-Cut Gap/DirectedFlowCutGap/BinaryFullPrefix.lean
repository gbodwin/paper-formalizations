import DirectedFlowCutGap.BinarySamplerTrees

/-! Finite independent bits realize the entire actual tracked sampler record,
including literal binary counters, instruction counts and the returned ledger.
This is still one callback; whole tape/query composition and host runtime remain
separate. -/
namespace DirectedFlowCutGap.BinaryFullPrefix
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinaryBoundedSampler BinarySamplerMetadata
open FiniteDrawTrees LazyFairBitTrees MonadicBitSampler

def tree (bound fuel : Bits) (positive : 0<value bound) (state : Ledger) :
    FiniteDrawTrees.Tree (Output bound × Ledger) :=
  FiniteDrawTrees.map (fun r => (r,record state r))
    (BinaryBoundedSampler.draw BinarySamplerTrees.bit bound positive fuel)

theorem within (bound fuel : Bits) (positive : 0<value bound) (state : Ledger) :
    Within (BinaryTrackedPrefix.budget bound fuel) (tree bound fuel positive state) :=
  within_map (BinarySamplerTrees.draw_within bound fuel positive) _

theorem binary (bound fuel : Bits) (positive : 0<value bound) (state : Ledger) :
    Binary (tree bound fuel positive state) :=
  binary_map (BinarySamplerTrees.draw_binary bound fuel positive) _

theorem execute_bit {M : Type → Type} [Monad M] [LawfulMonad M] (b : M (Fin 2)) :
    execute (liftBit b) BinarySamplerTrees.bit = (fun i : Fin 2 => decide (i.val=1)) <$> b := by
  simp only [BinarySamplerTrees.bit,execute,liftBit_two]
  rw [map_eq_pure_bind]

theorem execute_tree {M : Type → Type} [Monad M] [LawfulMonad M]
    (b : M (Fin 2)) (bound fuel : Bits) (positive : 0<value bound) (state : Ledger) :
    execute (liftBit b) (tree bound fuel positive state) =
      (trackedDraw ((fun i : Fin 2 => decide (i.val=1)) <$> b) bound positive fuel).run state := by
  rw [tree,execute_map,BinarySamplerTrees.draw_execute,execute_bit]
  simp only [trackedDraw,StateT.run,map_eq_pure_bind]

/-- No output projection is discarded by this equality: the full record,
ledger and source-state transition are those of the actual callback. -/
theorem same_stream (bound fuel : Bits) (positive : 0<value bound) (state : Ledger) :
    ((trackedDraw BinaryTrackedPrefix.next bound positive fuel).run state) =
      FiniteBinaryPrefix.run (tree bound fuel positive state) :=
  (execute_tree FiniteBinaryPrefix.next bound fuel positive state).symm

noncomputable section
/-- Full-record law, including operation instrumentation, from a fixed
independent prefix of the proved worst-case length. -/
theorem output_law (bound fuel : Bits) (positive : 0<value bound) (state : Ledger) :
    (FiniteBinaryPrefix.prefixLaw (BinaryTrackedPrefix.budget bound fuel)).map (fun xs =>
      (((trackedDraw BinaryTrackedPrefix.next bound positive fuel).run state).run xs).1) =
      (trackedDraw BinaryWeightedSamplingLaw.fairBit bound positive fuel).run state := by
  rw [same_stream,FiniteBinaryPrefix.output_law (within bound fuel positive state)
    (binary bound fuel positive state)]
  calc
    _ = execute (liftBit (PMF.uniformOfFintype (Fin 2))) (tree bound fuel positive state) :=
      (BinaryWeightedSamplingLaw.execute_binary_ideal (binary bound fuel positive state)).symm
    _ = _ := by
      simpa only [BinaryWeightedSamplingLaw.fairBit,PMF.monad_map_eq_map] using
        execute_tree (PMF.uniformOfFintype (Fin 2)) bound fuel positive state

end
end DirectedFlowCutGap.BinaryFullPrefix
