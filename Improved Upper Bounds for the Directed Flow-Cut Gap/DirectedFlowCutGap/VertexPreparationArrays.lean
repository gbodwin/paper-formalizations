import DirectedFlowCutGap.VertexGraphArrayLayout
import DirectedFlowCutGap.BinaryHeavyPreparation
import DirectedFlowCutGap.BinaryPortPreparation

/-! Match the stored arrays to the heavy-vertex and port preparations used by
both paid vertex modes. The shortcut search itself has separate accounting. -/
namespace DirectedFlowCutGap.VertexPreparationArrays

open EncodedArrayStorage EncodedUnitCostReplication IntegralNetworkFlow
open BinaryArrayNestedStorage (Code WithChildren Grid gridSchedule)
open ArrayMaterializationLayout (flat copyList)
open VertexGraphArrayLayout (Fields graphCode)

def heavyCode (n m : ℕ) : Code := flat n++flat n++copyList m++flat m++graphCode m

def portCode (n m : ℕ) : Code :=
  flat n++flat n++gridSchedule (3*n) (3*n)++flat (3*n)++gridSchedule (3*n) (3*n)++
    gridSchedule (3*n) (3*n)++copyList m++flat m++graphCode m

set_option maxHeartbeats 1500000 in
theorem heavy {n : ℕ} (D : Input n) (t : RawNonnegativeRational.Code) :
    let mask := (BinaryVertexReductionArithmetic.batch fun i : Fin n => BinaryRawRational.le t D.weights[i.val]).1
    let double := (BinaryVertexReductionArithmetic.batch fun i : Fin n =>
      BinaryRawRational.mul (RawNonnegativeRational.Code.ofNat 2) D.weights[i.val]).1
    let labels := (RetainedSurvivorEnumeration.scan mask (List.finRange n)).1
    let out := (BinaryHeavyPreparation.build D t).1
    out.heavy=mask ∧ out.size=labels.length ∧ out.labels.toList=labels.map Subtype.val ∧
    WithChildren mask (fun _ => []) (flat n) ∧ WithChildren double (fun _ => []) (flat n) ∧
    CopyExec labels [] labels.reverse (copyTrace labels) ∧
    ((reserveArray labels.length++copyTrace labels).map PackedArraySchedule.shape : Code)=copyList out.size ∧
    WithChildren out.labels (fun _ => []) (flat out.size) ∧ Fields out.data := by
  dsimp only [BinaryHeavyPreparation.build,EncodedHeavyVertexPreparation.buildWith]
  obtain ⟨copied,shape⟩ := ArrayMaterializationLayout.copy
    (RetainedSurvivorEnumeration.scan
      (BinaryVertexReductionArithmetic.batch fun i : Fin n => BinaryRawRational.le t D.weights[i.val]).1
      (List.finRange n)).1
  refine ⟨rfl,rfl,by simp,ArrayMaterializationLayout.batch _,ArrayMaterializationLayout.batch _,
    copied,shape,ArrayMaterializationLayout.map _ _,⟨?_,?_,?_⟩⟩
  · exact ArrayMaterializationLayout.matrix _
  · exact ArrayMaterializationLayout.ofFn _
  · exact ArrayMaterializationLayout.ofFn _

open EncodedShortcutReachability in
private theorem shortcut_arrays {m : ℕ} (P : EncodedShortcutReachability.Input m) :
    let E := ResidualSearch.Enumeration.fin m
    let F := Input.retainedDictionary E
    let intermediate := Vector.ofFn fun s : Fin m => Vector.ofFn fun t : Fin m => P.shortcut E F s t
    Grid intermediate (gridSchedule m m) ∧ Grid P.materialize.adjacency (gridSchedule m m) := by
  refine ⟨ArrayMaterializationLayout.matrix _,?_⟩
  let E := ResidualSearch.Enumeration.fin m
  let F := Input.retainedDictionary E
  have same : P.materialize.adjacency=Vector.ofFn (fun s : Fin m => Vector.ofFn fun t : Fin m =>
      (P.shortcut E F s t).1) := by
    ext i hi j hj
    simpa only [Vector.getElem_ofFn,Fin.eta] using P.materialize_cell ⟨i,hi⟩ ⟨j,hj⟩
  rw [same]
  exact ArrayMaterializationLayout.matrix _

open EncodedPortPreparation in
set_option maxHeartbeats 1300000 in
theorem ports {n : ℕ} (D : Input n) :
    let data := portData D
    let E := ResidualSearch.Enumeration.fin (3*n)
    let F := EncodedShortcutReachability.Input.retainedDictionary E
    let intermediate := Vector.ofFn fun s : Fin (3*n) => Vector.ofFn fun t : Fin (3*n) => data.shortcut E F s t
    let survivors := (RetainedSurvivorEnumeration.scan data.removed (List.finRange (3*n))).1
    let out := (BinaryPortPreparation.build D).1
    Grid data.adjacency (gridSchedule (3*n) (3*n)) ∧ WithChildren data.removed (fun _ => []) (flat (3*n)) ∧
    Grid intermediate (gridSchedule (3*n) (3*n)) ∧ Grid data.materialize.adjacency (gridSchedule (3*n) (3*n)) ∧
    out.size=survivors.length ∧ out.ports.toList=survivors.map Subtype.val ∧
    CopyExec survivors [] survivors.reverse (copyTrace survivors) ∧
    ((reserveArray survivors.length++copyTrace survivors).map PackedArraySchedule.shape : Code)=copyList out.size ∧
    WithChildren out.ports (fun _ => []) (flat out.size) ∧ Fields out.data := by
  let data := portData D
  obtain ⟨scratch,adjacency⟩ := shortcut_arrays data
  let survivors := (RetainedSurvivorEnumeration.scan data.removed (List.finRange (3*n))).1
  obtain ⟨copied,shape⟩ := ArrayMaterializationLayout.copy survivors
  rw [BinaryPortPreparation.build_value]
  dsimp only [EncodedUnitCostPreparation.build,EncodedUnitCostPreparation.buildWith]
  refine ⟨ArrayMaterializationLayout.matrix _,ArrayMaterializationLayout.ofFn _,scratch,adjacency,
    rfl,by simp,copied,shape,ArrayMaterializationLayout.map _ _,⟨?_,?_,?_⟩⟩
  · exact ArrayMaterializationLayout.matrix _
  · exact ArrayMaterializationLayout.ofFn _
  · exact ArrayMaterializationLayout.ofFn _

end DirectedFlowCutGap.VertexPreparationArrays
