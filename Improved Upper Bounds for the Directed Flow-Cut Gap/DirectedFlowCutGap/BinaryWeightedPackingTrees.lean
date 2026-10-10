import DirectedFlowCutGap.BinaryPackingTrees
import DirectedFlowCutGap.BinaryTicketTrees
import DirectedFlowCutGap.BinaryWeightedPackingConfidence

/-! Whole-program interpreter rules for the actual zero-safe packing body,
its complete final weighted ticket record and its computed confidence fuel. -/
namespace DirectedFlowCutGap.BinaryWeightedPackingTrees
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinaryFractionalRows BinaryZeroAvoidingProvider
open FiniteDrawTrees LazyFairBitTrees MonadicBitSampler
variable {n : ℕ} (w : Row n) (columns : Set (FractionalCover.Column n))
variable (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column n)∉columns)
variable (draw : CutProvider FiniteDrawTrees.Tree columns)

section Execute
variable {M : Type → Type} [Monad M] [LawfulMonad M]
variable (sample : (k : ℕ) → 0<k → M (Fin k))

theorem auxiliary_execute (row : Row n) :
    execute sample (auxiliaryProvider w columns hS hempty draw row)=
      auxiliaryProvider w columns hS hempty (fun c => execute sample (draw c)) row := by
  unfold auxiliaryProvider
  change execute sample (FiniteDrawTrees.bind _ _)=_
  rw [execute_bind]
  rfl

theorem run_execute (fuel : Bits) :
    execute sample (BinaryWeightedPacking.run w columns hS hempty draw BinarySamplerTrees.bit fuel)=
      BinaryWeightedPacking.run w columns hS hempty (fun c => execute sample (draw c))
        (execute sample BinarySamplerTrees.bit) fuel := by
  unfold BinaryWeightedPacking.run
  change execute sample (FiniteDrawTrees.bind _ _)=_
  rw [execute_bind,BinaryPackingTrees.solve_execute]
  have he : (fun row => execute sample (auxiliaryProvider w columns hS hempty draw row))=
      auxiliaryProvider w columns hS hempty (fun c => execute sample (draw c)) :=
    funext (auxiliary_execute w columns hS hempty draw sample)
  rw [he]
  congr 1
  funext history
  change execute sample (FiniteDrawTrees.bind _ _)=_
  rw [execute_bind,BinaryTicketTrees.events_execute]
  rfl

theorem confidence_execute (resources width : Bits) :
    execute sample (BinaryWeightedPackingConfidence.run w columns hS hempty draw
      BinarySamplerTrees.bit resources width)=
      BinaryWeightedPackingConfidence.run w columns hS hempty (fun c => execute sample (draw c))
        (execute sample BinarySamplerTrees.bit) resources width := by
  unfold BinaryWeightedPackingConfidence.run
  change execute sample (FiniteDrawTrees.bind _ _)=_
  rw [execute_bind,run_execute]
  rfl
end Execute

variable (hdraw : ∀ row,Binary (draw row))

theorem auxiliary_binary (row : Row n) :
    Binary (auxiliaryProvider w columns hS hempty draw row) :=
  binary_bind (hdraw _) _ (fun _ => .pure _)

theorem run_binary (fuel : Bits) :
    Binary (BinaryWeightedPacking.run w columns hS hempty draw BinarySamplerTrees.bit fuel) := by
  apply binary_bind (BinaryPackingTrees.solve_binary _ _ _
    (auxiliary_binary w columns hS hempty draw hdraw))
  intro history
  exact binary_bind (BinaryTicketTrees.events_binary _ _) _ (fun _ => .pure _)

theorem confidence_binary (resources width : Bits) :
    Binary (BinaryWeightedPackingConfidence.run w columns hS hempty draw
      BinarySamplerTrees.bit resources width) :=
  binary_bind (run_binary w columns hS hempty draw hdraw _) _ (fun _ => .pure _)

end DirectedFlowCutGap.BinaryWeightedPackingTrees
