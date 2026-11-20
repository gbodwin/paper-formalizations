import DirectedFlowCutGap.BinaryArrayNestedStorage
import DirectedFlowCutGap.BinaryEdgeGadget

/-! The measured gadget builds its label matrix, packs the selected vertex
list, and then fills adjacency, weight and price arrays for those vertices. -/
namespace DirectedFlowCutGap.EdgeGadgetArrayStorage

open EncodedArrayStorage Polynomial
open BinaryArrayNestedStorage (Code Grid WithChildren cellBudget cellBudget_eval cellBudget_mono
  copyBudget copyBudget_eval copyBudget_mono gridSchedule schedule flat_bounds grid_bounds)
open EncodedEdgeGadget (Input)

def codeFor (n size : ℕ) : Code :=
  let vertices := reserveArray size ++ copyTrace (List.replicate size ())
  let field := schedule size (fun _ => [])
  gridSchedule n n++vertices++gridSchedule size size++field++field

theorem for_build {n : ℕ} (D : Input n) :
    let g := (BinaryEdgeGadget.buildWithControl D).1.1
    Grid g.labels (gridSchedule n n) ∧
    (∃ selected : List _, selected.toArray=g.vertices.toArray ∧
      CopyExec selected [] selected.reverse (copyTrace selected) ∧
      ((reserveArray g.size++copyTrace selected).map PackedArraySchedule.shape : Code)=
        reserveArray g.size++copyTrace (List.replicate g.size ())) ∧
    Grid g.data.adjacency (gridSchedule g.size g.size) ∧
    WithChildren g.data.weights (fun _ => []) (schedule g.size (fun _ => [])) ∧
    WithChildren g.data.costs (fun _ => []) (schedule g.size (fun _ => [])) := by
  let g := (BinaryEdgeGadget.buildWithControl D).1.1
  have labels : ∃ code, Grid g.labels code ∧ code.length ≤ copyBudget n+n*copyBudget n ∧
      fresh code ≤ cellBudget n+n*cellBudget n := by
    unfold g BinaryEdgeGadget.buildWithControl BinaryEdgeGadget.labelsWithControl
    apply BinaryArrayNestedStorage.grid
    intro i
    apply BinaryArrayBatch.runWithChildWork_storage
  have adjacency : ∃ code, Grid g.data.adjacency code ∧ code.length ≤ copyBudget g.size+g.size*copyBudget g.size ∧
      fresh code ≤ cellBudget g.size+g.size*cellBudget g.size := by
    unfold g BinaryEdgeGadget.buildWithControl
    apply BinaryArrayNestedStorage.grid
    intro i
    apply BinaryArrayBatch.runWithChildWork_storage
  have weights : BinaryArrayBatch.StorageModel g.data.weights := by
    unfold g BinaryEdgeGadget.buildWithControl
    apply BinaryArrayBatch.runWithChildWork_storage
  have prices : BinaryArrayBatch.StorageModel g.data.costs := by
    unfold g BinaryEdgeGadget.buildWithControl
    apply BinaryArrayBatch.runWithChildWork_storage
  obtain ⟨_,labels,_,_⟩ := labels
  obtain ⟨_,adjacency,_,_⟩ := adjacency
  obtain ⟨_,weight,_,_⟩ := BinaryArrayNestedStorage.alone weights
  obtain ⟨_,price,_,_⟩ := BinaryArrayNestedStorage.alone prices
  refine ⟨BinaryArrayNestedStorage.grid_schedule_eq labels ▸ labels, ?_,
    BinaryArrayNestedStorage.grid_schedule_eq adjacency ▸ adjacency,
    BinaryArrayNestedStorage.schedule_eq weight ▸ weight,BinaryArrayNestedStorage.schedule_eq price ▸ price⟩
  let selected := g.vertices.toList
  refine ⟨selected,?_,by simpa using copy_exec selected [],?_⟩
  · change g.vertices.toArray.toList.toArray=g.vertices.toArray
    simp
  · simp only [List.map_append,BinaryArrayNestedStorage.copy_shape,selected,Vector.length_toList]
    rfl

theorem bounds : ∃ cells copies : Polynomial ℕ, ∀ {n : ℕ} (D : Input n),
    let g := (BinaryEdgeGadget.buildWithControl D).1.1
    fresh (codeFor n g.size) ≤ cells.eval n ∧ (codeFor n g.size).length ≤ copies.eval n := by
  let m := BinaryEdgeGadget.dimension (X : Polynomial ℕ)
  let cells := (X+1)*cellBudget X+(m+3)*cellBudget m+(m+2)
  let copies := (X+1)*copyBudget X+(m+3)*copyBudget m+(4*m+4)
  refine ⟨cells,copies,fun {n} D => ?_⟩
  let g := (BinaryEdgeGadget.buildWithControl D).1.1
  let k := g.size
  have size : k ≤ m.eval n := by
    simp only [m,BinaryEdgeGadget.dimension,eval_mul,eval_add,eval_ofNat,eval_X]
    have same := congrArg Prod.fst (BinaryEdgeGadget.build_control_projection D)
    change (BinaryEdgeGadget.buildWithControl D).1.1.size ≤ BinaryEdgeGadget.dimension n
    rw [same]
    exact BinaryEdgeGadget.size_le D
  have factor : k+3 ≤ m.eval n+3 := Nat.add_le_add_right size _
  have slots := Nat.mul_le_mul factor (cellBudget_mono size)
  have operations := Nat.mul_le_mul factor (copyBudget_mono size)
  have flat := flat_bounds k
  have graph := grid_bounds k
  have labels := grid_bounds n
  change fresh (codeFor n k) ≤ cells.eval n ∧ (codeFor n k).length ≤ copies.eval n
  simp only [codeFor,fresh_append,List.length_append,reserveArray_fresh,reserveArray_length,copyTrace_fresh,
    copyTrace_length,List.length_replicate,cells,copies,eval_add,eval_mul,eval_X,eval_ofNat,eval_one,
    cellBudget_eval,copyBudget_eval,Nat.add_zero]
  simp only [Nat.add_mul,Nat.one_mul] at graph slots operations labels ⊢
  constructor <;> omega

end DirectedFlowCutGap.EdgeGadgetArrayStorage
