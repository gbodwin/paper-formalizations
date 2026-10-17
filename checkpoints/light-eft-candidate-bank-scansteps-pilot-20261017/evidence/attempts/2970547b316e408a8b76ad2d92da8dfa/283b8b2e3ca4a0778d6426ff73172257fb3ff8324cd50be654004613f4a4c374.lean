import LightEFTSpanners.StoredCandidateBankPreparation
namespace LightEFTSpanners.StoredCandidateBankPreparation.ScanStepsComparison
open StoredCandidatePreparation (Input)
def scanSteps (W : StoredRecords.Weights) : List Input → ℕ :=
  List.rec (motive := fun _ => ℕ) 1
    (fun r _ rest => StoredCandidatePreparation.steps W r+2+rest)
theorem scanSteps_eq_prior (W : StoredRecords.Weights) (rs : List Input) :
    scanSteps W rs = LightEFTSpanners.StoredCandidateBankPreparation.scanSteps W rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    exact congrArg (fun rest => StoredCandidatePreparation.steps W r+2+rest) ih
#print axioms scanSteps_eq_prior
end LightEFTSpanners.StoredCandidateBankPreparation.ScanStepsComparison
