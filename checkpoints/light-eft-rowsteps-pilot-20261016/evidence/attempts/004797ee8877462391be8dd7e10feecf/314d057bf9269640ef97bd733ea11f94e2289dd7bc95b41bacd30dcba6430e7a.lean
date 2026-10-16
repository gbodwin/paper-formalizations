import LightEFTSpanners.StoredWeightLookup
namespace LightEFTSpanners.StoredWeightLookup.RowStepsComparison
def rowSteps : ℕ → List ℚ → ℕ :=
  fun j row => List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1)
    (fun _ _ next i => match i with | 0 => 1 | k+1 => next k+1) row j
theorem rowSteps_eq_prior (j : ℕ) (row : List ℚ) :
    rowSteps j row = LightEFTSpanners.StoredWeightLookup.rowSteps j row := by
  induction row generalizing j with
  | nil => cases j <;> rfl
  | cons w ws ih =>
    cases j with
    | zero => rfl
    | succ j => exact congrArg (fun n : ℕ => n+1) (ih j)
#print axioms rowSteps_eq_prior
end LightEFTSpanners.StoredWeightLookup.RowStepsComparison
