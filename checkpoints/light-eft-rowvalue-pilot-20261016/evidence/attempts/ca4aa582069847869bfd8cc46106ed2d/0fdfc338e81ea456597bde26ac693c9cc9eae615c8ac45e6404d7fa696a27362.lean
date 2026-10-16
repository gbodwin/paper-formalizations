import LightEFTSpanners.StoredWeightLookup
namespace LightEFTSpanners.StoredWeightLookup.RowValueComparison
def rowValue : ℕ → List ℚ → ℚ :=
  fun j row => List.rec (motive := fun _ => ℕ → ℚ) (fun _ => 0)
    (fun w _ next i => match i with | 0 => w | k+1 => next k) row j
theorem rowValue_eq_prior (j : ℕ) (row : List ℚ) :
    rowValue j row = LightEFTSpanners.StoredWeightLookup.rowValue j row := by
  induction row generalizing j with
  | nil => rfl
  | cons w ws ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j
#print axioms rowValue_eq_prior
end LightEFTSpanners.StoredWeightLookup.RowValueComparison
