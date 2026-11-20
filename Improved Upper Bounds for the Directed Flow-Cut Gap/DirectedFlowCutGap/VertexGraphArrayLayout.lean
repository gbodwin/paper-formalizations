import DirectedFlowCutGap.ArrayMaterializationLayout
import DirectedFlowCutGap.EncodedUnitCostPreparation

/-! The survivor and replica labels are copied from their actual lists.
The retained graph records use the corresponding indexed array callbacks. -/
namespace DirectedFlowCutGap.VertexGraphArrayLayout

open Polynomial EncodedArrayStorage EncodedUnitCostReplication
open ArrayMaterializationLayout (flat copyList)
open BinaryArrayNestedStorage (Code WithChildren Grid gridSchedule copyBudget cellBudget)

def graphCode (n : ℕ) : Code := gridSchedule n n++flat n++flat n

def replicaCode (n : ℕ) : Code := copyList n++graphCode n

structure Fields {n : ℕ} (data : Input n) : Prop where
  adjacency : Grid data.adjacency (gridSchedule n n)
  weights : WithChildren data.weights (fun _ => []) (flat n)
  prices : WithChildren data.costs (fun _ => []) (flat n)

theorem replica {n : ℕ} (D : Input n) (k : Vector ℕ n) :
    let out := materialize D k
    out.labels.toList=cloneList k ∧
    CopyExec (cloneList k) [] (cloneList k).reverse (copyTrace (cloneList k)) ∧
    ((reserveArray (cloneList k).length++copyTrace (cloneList k)).map PackedArraySchedule.shape : Code)=
      copyList (cloneList k).length ∧ Fields out.input := by
  obtain ⟨copied,shape⟩ := ArrayMaterializationLayout.copy (cloneList k)
  refine ⟨by simp [labelVector],copied,shape,⟨?_,?_,?_⟩⟩
  · exact ArrayMaterializationLayout.matrix _
  · exact ArrayMaterializationLayout.ofFn _
  · exact ArrayMaterializationLayout.replicate _ _

theorem graph_counts (n : ℕ) :
    (graphCode n).length ≤ (n+3)*copyBudget n ∧ fresh (graphCode n) ≤ (n+3)*cellBudget n := by
  have matrix := BinaryArrayNestedStorage.grid_bounds n
  have fields : (flat n).length ≤ copyBudget n ∧ fresh (flat n) ≤ cellBudget n :=
    BinaryArrayNestedStorage.flat_bounds n
  simp only [graphCode,List.length_append,fresh_append,Nat.add_mul,Nat.one_mul] at matrix ⊢
  constructor <;> omega

theorem replica_counts (n : ℕ) :
    (replicaCode n).length ≤ (n+3)*copyBudget n+4*n+4 ∧
    fresh (replicaCode n) ≤ (n+3)*cellBudget n+n+2 := by
  have graph := graph_counts n
  obtain ⟨steps,extent⟩ := ArrayMaterializationLayout.copy_counts n
  simp only [replicaCode,List.length_append,fresh_append,steps,extent]
  constructor <;> omega

end DirectedFlowCutGap.VertexGraphArrayLayout
