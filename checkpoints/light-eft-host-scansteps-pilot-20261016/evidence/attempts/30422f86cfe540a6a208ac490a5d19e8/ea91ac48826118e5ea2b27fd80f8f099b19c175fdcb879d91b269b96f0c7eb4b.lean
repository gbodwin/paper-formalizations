import LightEFTSpanners.StoredHostPreparation
namespace LightEFTSpanners.StoredHostPreparation.ScanStepsComparison
def scanSteps (e : StoredEdges.Edge) : List Record → ℕ :=
  List.rec (motive := fun _ => ℕ) 1
    (fun r _ rest => StoredEdges.steps e r.eligibleEdges+2+rest)
theorem scanSteps_eq_prior (e : StoredEdges.Edge) (rs : List Record) :
    scanSteps e rs = LightEFTSpanners.StoredHostPreparation.scanSteps e rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    exact congrArg (fun rest => StoredEdges.steps e r.eligibleEdges+2+rest) ih
#print axioms scanSteps_eq_prior
end LightEFTSpanners.StoredHostPreparation.ScanStepsComparison
