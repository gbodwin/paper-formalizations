import DirectedFlowCutGap.ArrayMaterializationLayout
import DirectedFlowCutGap.EncodedHeavyVertexOutput
import DirectedFlowCutGap.EncodedUniformOutput

/-! The mask pullbacks use the actual chosen labels and stored masks.
Associate their intermediate and final arrays with the modeled tabulations. -/
namespace DirectedFlowCutGap.VertexMaskProjectionArrays

open BinaryArrayNestedStorage (WithChildren)
open ArrayMaterializationLayout (flat)
open EncodedUnitCostPreparation (Prepared)
open EncodedUnitCostReplication

theorem port {n : ℕ} (out : Prepared n) (mask : Vector Bool out.size) :
    WithChildren (out.pullbackMaskWithCost mask).1 (fun _ => []) (flat n) :=
  ArrayMaterializationLayout.ofFn _

theorem parallel {n : ℕ} (out : Prepared n) (k : Vector ℕ out.size) (replica : Replica k)
    (mask : Vector Bool (cloneList k).length) :
    let fiber := (fullFiberMaskWithCost k replica.labels mask).1
    WithChildren fiber (fun _ => []) (flat out.size) ∧
      WithChildren (out.pullbackSampleWithCost k replica mask).1 (fun _ => []) (flat n) :=
  ⟨ArrayMaterializationLayout.ofFn _,port out _⟩

theorem uniform {n : ℕ} {k : Vector ℕ (3*n)} (out : EncodedUniformChain.Chain k)
    (mask : Vector Bool out.size) :
    WithChildren (EncodedUniformOutput.originalView out).ports (fun _ => []) (flat out.size) ∧
      WithChildren (EncodedUniformOutput.originalMaskWithCost out mask).1 (fun _ => []) (flat n) :=
  ⟨ArrayMaterializationLayout.map _ _,port (EncodedUniformOutput.originalView out) mask⟩

theorem heavy {n : ℕ} (out : EncodedHeavyVertexPreparation.Residual n) (mask : Vector Bool out.size) :
    let view := EncodedHeavyVertexPreparation.liftView out
    WithChildren view.ports (fun _ => []) (flat out.size) ∧
      WithChildren (view.pullbackMaskWithCost mask).1 (fun _ => []) (flat n) ∧
      WithChildren (EncodedHeavyVertexPreparation.combinedMaskWithCost out mask).1 (fun _ => []) (flat n) :=
  ⟨ArrayMaterializationLayout.map _ _,port (EncodedHeavyVertexPreparation.liftView out) mask,
    ArrayMaterializationLayout.ofFn _⟩

end DirectedFlowCutGap.VertexMaskProjectionArrays
