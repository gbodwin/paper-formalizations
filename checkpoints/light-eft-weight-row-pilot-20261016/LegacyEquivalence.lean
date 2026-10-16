import LightEFTSpanners.StoredOriginalWeightMatrix
namespace LightEFTSpanners.StoredOriginalWeightMatrix.RowComparison
def row (bank : StoredOriginalWeightLookup.Bank) (i : ℕ) : ℕ → ℕ → List ℚ :=
  fun j k => Nat.rec (motive := fun _ => ℕ → List ℚ) (fun _ => [])
    (fun _ next col => StoredOriginalWeightLookup.value (i,col) bank::next (col+1)) k j
theorem row_eq_prior (bank : StoredOriginalWeightLookup.Bank) (i j k : ℕ) :
    row bank i j k = LightEFTSpanners.StoredOriginalWeightMatrix.row bank i j k := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    exact congrArg (List.cons (StoredOriginalWeightLookup.value (i,j) bank)) (ih (j+1))
#print axioms row_eq_prior
end LightEFTSpanners.StoredOriginalWeightMatrix.RowComparison
