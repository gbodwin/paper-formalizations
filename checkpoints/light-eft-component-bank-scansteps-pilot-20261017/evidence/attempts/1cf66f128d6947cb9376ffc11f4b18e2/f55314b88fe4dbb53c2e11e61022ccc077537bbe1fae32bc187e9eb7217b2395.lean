import LightEFTSpanners.StoredComponentBank
namespace LightEFTSpanners.StoredComponentBank.ScanStepsComparison
open StoredComponentCandidate (Input)
def scanSteps (W : StoredRecords.Weights) : List Input → ℕ :=
  List.rec (motive := fun _ => ℕ) 1
    (fun r _ rest => StoredComponentCandidate.steps W r+2+rest)
theorem scanSteps_eq_prior (W : StoredRecords.Weights) (rs : List Input) :
    scanSteps W rs = LightEFTSpanners.StoredComponentBank.scanSteps W rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    exact congrArg (fun rest => StoredComponentCandidate.steps W r+2+rest) ih
#print axioms scanSteps_eq_prior
end LightEFTSpanners.StoredComponentBank.ScanStepsComparison
