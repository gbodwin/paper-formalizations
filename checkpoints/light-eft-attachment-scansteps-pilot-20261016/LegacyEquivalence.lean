import LightEFTSpanners.StoredForestDrawAttachment
namespace LightEFTSpanners.StoredForestDrawAttachment.ScanStepsComparison
def scanSteps (n : ℕ) (bank : StoredDrawLookup.Bank) : List Record → ℕ :=
  List.rec (motive := fun _ => ℕ) 1
    (fun r _ rest => StoredDrawLookup.steps (key n r) bank+2+rest)
theorem scanSteps_eq_prior (n : ℕ) (bank : StoredDrawLookup.Bank) (rs : List Record) :
    scanSteps n bank rs = LightEFTSpanners.StoredForestDrawAttachment.scanSteps n bank rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    exact congrArg (fun rest => StoredDrawLookup.steps (key n r) bank+2+rest) ih
#print axioms scanSteps_eq_prior
end LightEFTSpanners.StoredForestDrawAttachment.ScanStepsComparison
