import DirectedFlowCutGap.BinaryArrayNestedStorage
import DirectedFlowCutGap.EncodedUnitCostReplication
import DirectedFlowCutGap.ChargedVertexModes

/-! A per-round layout and its polynomial bounds in the typed graph dimension
and the shared trial count. The outer traversals use the same interface for
cutoffs alone and for preparation followed by cutoffs. -/
namespace DirectedFlowCutGap.RoundArrayLayout

open BinaryArithmetic EncodedArrayStorage Polynomial
open BinaryArrayNestedStorage (Code)

abbrev Runner := {n : ℕ} → ChargedVertexModes.Mode → ℕ → EncodedUnitCostReplication.Input n → Bits → Code → Prop

def Bounded (layout : Runner) : Prop :=
  ∃ cells copies : Polynomial ℕ, ∀ {n : ℕ} (mode : ChargedVertexModes.Mode) (T : ℕ)
    (input : EncodedUnitCostReplication.Input n) (tape : Bits),
    ∃ code : Code, layout mode T input tape code ∧ fresh code ≤ cells.eval (n+T) ∧ code.length ≤ copies.eval (n+T)

end DirectedFlowCutGap.RoundArrayLayout
