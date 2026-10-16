import LightEFTSpanners.StoredWeightLookup
namespace LightEFTSpanners.StoredWeightLookup.StepsComparison
def steps : ℕ → ℕ → StoredRecords.Weights → ℕ :=
  fun i j W => List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1)
    (fun row _ next k => match k with | 0 => rowSteps j row+1 | k+1 => next k+1) W i
theorem steps_eq_prior (i j : ℕ) (W : StoredRecords.Weights) :
    steps i j W = LightEFTSpanners.StoredWeightLookup.steps i j W := by
  induction W generalizing i with
  | nil => cases i <;> rfl
  | cons row rows ih =>
    cases i with
    | zero => rfl
    | succ i => exact congrArg (fun n : ℕ => n+1) (ih i)
#print axioms steps_eq_prior
end LightEFTSpanners.StoredWeightLookup.StepsComparison
