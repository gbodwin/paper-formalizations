import LightEFTSpanners.StoredWeightLookup
namespace LightEFTSpanners.StoredWeightLookup.ValueComparison
def value : ℕ → ℕ → StoredRecords.Weights → ℚ :=
  fun i j W => List.rec (motive := fun _ => ℕ → ℚ) (fun _ => 0)
    (fun row _ next k => match k with | 0 => rowValue j row | k+1 => next k) W i
theorem value_eq_prior (i j : ℕ) (W : StoredRecords.Weights) :
    value i j W = LightEFTSpanners.StoredWeightLookup.value i j W := by
  induction W generalizing i with
  | nil => cases i <;> rfl
  | cons row rows ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i
#print axioms value_eq_prior
end LightEFTSpanners.StoredWeightLookup.ValueComparison
