import LightEFTSpanners.StoredOriginalWeightMatrix
namespace LightEFTSpanners.StoredOriginalWeightMatrix.RowsComparison
def rows (bank : StoredOriginalWeightLookup.Bank) (n : ℕ) : ℕ → ℕ → StoredRecords.Weights :=
  fun i k => Nat.rec (motive := fun _ => ℕ → StoredRecords.Weights) (fun _ => [])
    (fun _ next start => row bank start 0 n::next (start+1)) k i
theorem rows_eq_prior (bank : StoredOriginalWeightLookup.Bank) (n i k : ℕ) :
    rows bank n i k = LightEFTSpanners.StoredOriginalWeightMatrix.rows bank n i k := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    exact congrArg (List.cons (row bank i 0 n)) (ih (i+1))
#print axioms rows_eq_prior
end LightEFTSpanners.StoredOriginalWeightMatrix.RowsComparison
