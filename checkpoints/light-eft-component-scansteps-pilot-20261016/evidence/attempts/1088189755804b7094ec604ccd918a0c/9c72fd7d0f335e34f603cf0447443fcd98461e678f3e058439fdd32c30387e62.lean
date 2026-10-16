import LightEFTSpanners.StoredComponentHostTrace
namespace LightEFTSpanners.StoredComponentHostFilter.ScanStepsComparison
def scanSteps (vs : List ℕ) : List StoredEdges.Edge → ℕ :=
  List.rec (motive := fun _ => ℕ) 1
    (fun e _ rest => edgeSteps vs e+rest)
theorem scanSteps_eq_prior (vs : List ℕ) (es : List StoredEdges.Edge) :
    scanSteps vs es = LightEFTSpanners.StoredComponentHostFilter.scanSteps vs es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    exact congrArg (fun rest => edgeSteps vs e+rest) ih
#print axioms scanSteps_eq_prior
end LightEFTSpanners.StoredComponentHostFilter.ScanStepsComparison
