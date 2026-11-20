import DirectedFlowCutGap.BinaryArrayNestedStorage

/-! The same indexed callbacks supply the values in ordinary array
materialization and in the measured persistent-array layout. -/
namespace DirectedFlowCutGap.ArrayMaterializationLayout

open EncodedArrayStorage
open BinaryArrayNestedStorage (Code WithChildren Grid schedule gridSchedule)

def flat (n : ℕ) : Code := schedule n (fun _ => [])

def copyList (n : ℕ) : Code := reserveArray n++copyTrace (List.replicate n ())

theorem batch {A : Type} {n : ℕ} (f : Fin n → A × ℕ) :
    WithChildren (BinaryArrayBatch.run f).1.1 (fun _ => []) (flat n) :=
  BinaryArrayNestedStorage.flat_schedule (BinaryArrayBatch.run_storage f)

theorem ofFn {A : Type} {n : ℕ} (f : Fin n → A) :
    WithChildren (Vector.ofFn f) (fun _ => []) (flat n) := by
  let addFee (i : Fin n) := (f i,0)
  have same : (BinaryArrayBatch.run addFee).1.1=Vector.ofFn f :=
    congrArg Prod.fst (BinaryArrayBatch.run_value addFee)
  exact same ▸ batch addFee

theorem map {A B : Type} {n : ℕ} (f : A → B) (xs : Vector A n) :
    WithChildren (xs.map f) (fun _ => []) (flat n) := by
  have same : xs.map f=Vector.ofFn fun i : Fin n => f xs[i.val] := by
    ext i hi
    simp
  rw [same]
  exact ofFn _

theorem replicate {A : Type} (x : A) (n : ℕ) :
    WithChildren (Vector.replicate n x) (fun _ => []) (flat n) := by
  have same : Vector.replicate n x=Vector.ofFn (fun _ : Fin n => x) := by
    ext i hi
    simp
  rw [same]
  exact ofFn _

theorem matrix {A : Type} {m n : ℕ} (f : Fin m → Fin n → A) :
    Grid (Vector.ofFn fun i => Vector.ofFn (f i)) (gridSchedule m n) := by
  let row (i : Fin m) (j : Fin n) := (f i j,0)
  let entry (i : Fin m) := (((BinaryArrayBatch.run (row i)).1.1,0),0)
  have model := BinaryArrayNestedStorage.grid_schedule entry (fun i => BinaryArrayBatch.run_storage (row i))
  have cells : (BinaryArrayBatch.runWithChildWork entry).1.1 = Vector.ofFn (fun i => Vector.ofFn (f i)) := by
    rw [congrArg Prod.fst (BinaryArrayBatch.runWithChildWork_value entry)]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn,entry,congrArg Prod.fst (BinaryArrayBatch.run_value (row ⟨i,hi⟩))]
    rfl
  exact cells ▸ model

theorem copy {A : Type} (xs : List A) :
    CopyExec xs [] xs.reverse (copyTrace xs) ∧
      ((reserveArray xs.length++copyTrace xs).map PackedArraySchedule.shape : Code)=copyList xs.length := by
  refine ⟨by simpa using copy_exec xs [],?_⟩
  simp only [copyList,List.map_append,BinaryArrayNestedStorage.copy_shape]
  rfl

theorem copy_counts (n : ℕ) : (copyList n).length=4*n+4 ∧ fresh (copyList n)=n+2 := by
  constructor
  · simp only [copyList,List.length_append,reserveArray_length,copyTrace_length,List.length_replicate]
    omega
  · simp only [copyList,fresh_append,reserveArray_fresh,copyTrace_fresh,Nat.add_zero]

end DirectedFlowCutGap.ArrayMaterializationLayout
