import LightEFTSpanners.StoredCanonicalHosts
namespace LightEFTSpanners.StoredCanonicalHosts.ScanStepsComparison
def scanSteps (edges : List StoredEdges.Edge) : List Component → ℕ :=
  List.rec (motive := fun _ => ℕ) 1
    (fun r _ rest => StoredComponentHostFilter.steps r.2 edges+2+rest)
theorem scanSteps_eq_prior (edges : List StoredEdges.Edge) (rs : List Component) :
    scanSteps edges rs = LightEFTSpanners.StoredCanonicalHosts.scanSteps edges rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    exact congrArg (fun rest => StoredComponentHostFilter.steps r.2 edges+2+rest) ih
#print axioms scanSteps_eq_prior
end LightEFTSpanners.StoredCanonicalHosts.ScanStepsComparison
