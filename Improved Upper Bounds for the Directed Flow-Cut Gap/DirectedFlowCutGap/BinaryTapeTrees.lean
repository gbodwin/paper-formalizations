import DirectedFlowCutGap.BinaryFullPrefixCost
import DirectedFlowCutGap.BinaryRetainedTape

/-! Full-record interpretation through both actual retained tape loops.
The original list control, binary index decoder and every ledger update are
preserved. The tree is proof-side syntax only. This file does not yet give a
whole-query finite-prefix budget or physical-runtime simulation. -/
namespace DirectedFlowCutGap.BinaryTapeTrees
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinarySamplerMetadata BinaryRetainedTape
open FiniteDrawTrees MonadicBitSampler

section Execute
variable {M : Type → Type} [Monad M] [LawfulMonad M]
variable (b : M (Fin 2))

abbrev boolBit := (fun i : Fin 2 => decide (i.val=1)) <$> b

private theorem tracked_execute (bound fuel : Bits) (positive : 0<value bound) (s : Ledger) :
    execute (liftBit b) ((trackedDraw BinarySamplerTrees.bit bound positive fuel).run s) =
      (trackedDraw (boolBit b) bound positive fuel).run s := by
  change execute (liftBit b) (BinaryFullPrefix.tree bound fuel positive s) = _
  exact BinaryFullPrefix.execute_tree b bound fuel positive s

theorem drawIndex_execute (fuel bound : Bits) {N : ℕ}
    (hb : value bound=N) (hN : 0<N) (s : Ledger) :
    execute (liftBit b) (drawIndex BinarySamplerTrees.bit fuel bound hb hN s) =
      drawIndex (boolBit b) fuel bound hb hN s := by
  unfold drawIndex
  change execute (liftBit b) (FiniteDrawTrees.bind _ _) = _
  rw [execute_bind,tracked_execute]
  rfl

theorem permutation_execute (fuel : Bits) {A : Type} (xs : List A)
    (bound : Bits) (hb : value bound=xs.length) (s : Ledger) :
    execute (liftBit b) (permutation BinarySamplerTrees.bit fuel xs bound hb s) =
      permutation (boolBit b) fuel xs bound hb s := by
  induction xs generalizing bound s with
  | nil => rfl
  | cons x xs ih =>
    simp only [permutation]
    change execute (liftBit b) (FiniteDrawTrees.bind _ _) = _
    rw [execute_bind,drawIndex_execute]
    congr 1
    funext j
    change execute (liftBit b) (FiniteDrawTrees.bind _ _) = _
    rw [execute_bind,ih]
    rfl

theorem cells_execute (fuel cutoff : Bits) {L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) {A : Type} (xs : List A) (s : Ledger) :
    execute (liftBit b) (cells BinarySamplerTrees.bit fuel cutoff hcut hL xs s) =
      cells (boolBit b) fuel cutoff hcut hL xs s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [cells]
    change execute (liftBit b) (FiniteDrawTrees.bind _ _) = _
    rw [execute_bind,drawIndex_execute]
    congr 1
    funext j
    change execute (liftBit b) (FiniteDrawTrees.bind _ _) = _
    rw [execute_bind,ih]
    rfl

theorem tape_execute (fuel cutoff : Bits) {L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) {A : Type} (xs : List A) (bound : Bits)
    (hb : value bound=xs.length) (s : Ledger) :
    execute (liftBit b) (tape BinarySamplerTrees.bit fuel cutoff hcut hL xs bound hb s) =
      tape (boolBit b) fuel cutoff hcut hL xs bound hb s := by
  unfold tape
  change execute (liftBit b) (FiniteDrawTrees.bind _ _) = _
  rw [execute_bind,permutation_execute]
  congr 1
  funext p
  change execute (liftBit b) (FiniteDrawTrees.bind _ _) = _
  rw [execute_bind,cells_execute]
  rfl

theorem sampleTape_execute (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) (a : RetainedGridState.PairFlags n) (s : Ledger) :
    execute (liftBit b) (sampleTape BinarySamplerTrees.bit fuel cutoff hcut hL a s) =
      sampleTape (boolBit b) fuel cutoff hcut hL a s := by
  unfold sampleTape
  change execute (liftBit b) (FiniteDrawTrees.bind _ _) = _
  rw [execute_bind,tape_execute]
  rfl

theorem callback_execute (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) (a : RetainedGridState.PairFlags n) (s : Ledger) :
    execute (liftBit b) ((callback BinarySamplerTrees.bit fuel cutoff hcut hL a).run s) =
      (callback (boolBit b) fuel cutoff hcut hL a).run s := by
  simp only [callback,StateT.run]
  change execute (liftBit b) (FiniteDrawTrees.bind _ _) = _
  rw [execute_bind,sampleTape_execute]
  rfl

end Execute
end DirectedFlowCutGap.BinaryTapeTrees
