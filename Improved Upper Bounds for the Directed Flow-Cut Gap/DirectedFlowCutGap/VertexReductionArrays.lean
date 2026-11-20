import DirectedFlowCutGap.VertexGraphArrayLayout
import DirectedFlowCutGap.BinaryVertexReductionArithmetic

/-! The measured reduction builds a threshold mask for zero objective. Its
positive branch retains normalized prices, counts, and the cloned graph. -/
namespace DirectedFlowCutGap.VertexReductionArrays

open EncodedArrayStorage EncodedUnitCostReplication
open BinaryArrayNestedStorage (Code WithChildren)
open ArrayMaterializationLayout (flat copyList)
open VertexGraphArrayLayout (Fields replicaCode)

def code {n : ℕ} : Input.Result n → Code
  | .zero _ _ => flat n
  | .replicated _ counts _ _ => flat n++flat n++replicaCode (cloneList counts).length

def Model {n : ℕ} : Input.Result n → Prop
  | .zero flags _ => WithChildren flags (fun _ => []) (flat n)
  | .replicated normalized counts stored _ =>
    WithChildren normalized (fun _ => []) (flat n) ∧ WithChildren counts (fun _ => []) (flat n) ∧
      stored.labels.toList=cloneList counts ∧
      CopyExec (cloneList counts) [] (cloneList counts).reverse (copyTrace (cloneList counts)) ∧
      ((reserveArray (cloneList counts).length++copyTrace (cloneList counts)).map PackedArraySchedule.shape : Code)=
        copyList (cloneList counts).length ∧ Fields stored.input

set_option maxHeartbeats 900000 in
theorem arrays {n : ℕ} (D : Input n) : Model (BinaryVertexReductionArithmetic.reduce D).1 := by
  unfold BinaryVertexReductionArithmetic.reduce
  dsimp only
  split
  · change WithChildren (BinaryVertexReductionArithmetic.zeroMask D).1 (fun _ => []) (flat n)
    exact ArrayMaterializationLayout.batch _
  · let sum := (BinaryVertexReductionArithmetic.totals D).1
    let norm := (BinaryVertexReductionArithmetic.normalized D sum).1
    let ks := (BinaryVertexReductionArithmetic.ceilings norm).1
    have priceLayout : WithChildren norm (fun _ => []) (flat n) := by
      dsimp only [norm,BinaryVertexReductionArithmetic.normalized,BinaryVertexReductionArithmetic.batch]
      exact ArrayMaterializationLayout.batch _
    have countLayout : WithChildren ks (fun _ => []) (flat n) := ArrayMaterializationLayout.batch _
    exact ⟨priceLayout,countLayout,VertexGraphArrayLayout.replica D ks⟩

end DirectedFlowCutGap.VertexReductionArrays
