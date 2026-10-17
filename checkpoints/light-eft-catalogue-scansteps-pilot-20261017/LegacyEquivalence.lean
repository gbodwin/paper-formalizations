import LightEFTSpanners.StoredComponentCatalogue
namespace LightEFTSpanners.StoredComponentCatalogue.ScanStepsComparison
open StoredComponentRecord (Input)
def scanSteps : List Input → ℕ :=
  List.rec (motive := fun _ => ℕ) 1
    (fun r _ rest => StoredComponentRecord.steps r+2+rest)
theorem scanSteps_eq_prior (rs : List Input) :
    scanSteps rs = LightEFTSpanners.StoredComponentCatalogue.scanSteps rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    exact congrArg (fun rest => StoredComponentRecord.steps r+2+rest) ih
#print axioms scanSteps_eq_prior
end LightEFTSpanners.StoredComponentCatalogue.ScanStepsComparison
