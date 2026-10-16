import LightEFTSpanners.StoredOriginalWeightExecutable

namespace LightEFTSpanners.StoredOriginalWeightMatrix

theorem row_ofFn (bank : StoredOriginalWeightLookup.Bank) (i j k : ℕ) :
    row bank i j k=List.ofFn (fun v : Fin k => StoredOriginalWeightLookup.value (i,j+v.val) bank) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    rw [row,List.ofFn_succ]
    simp only [Fin.val_zero,Nat.add_zero]
    congr 1
    rw [ih]
    congr 1
    funext v
    simp [Nat.add_comm,Nat.add_left_comm]

theorem rows_ofFn (bank : StoredOriginalWeightLookup.Bank) (n i k : ℕ) :
    rows bank n i k=List.ofFn (fun v : Fin k => row bank (i+v.val) 0 n) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    rw [rows,List.ofFn_succ]
    simp only [Fin.val_zero,Nat.add_zero]
    congr 1
    rw [ih]
    congr 1
    funext v
    simp [Nat.add_comm,Nat.add_left_comm]

theorem execute_encoded {n : ℕ} (bank : StoredOriginalWeightLookup.TypedBank n) :
    execute n (StoredOriginalWeightLookup.encode bank)=
      StoredRecords.encodeWeights (fun e => StoredOriginalWeightLookup.weight e bank) := by
  rw [execute_eq,rows_ofFn]
  unfold StoredRecords.encodeWeights
  congr 1
  funext i
  rw [row_ofFn]
  congr 1
  funext j
  simp only [Nat.zero_add]
  exact StoredOriginalWeightLookup.value_encoded i j bank
end LightEFTSpanners.StoredOriginalWeightMatrix
