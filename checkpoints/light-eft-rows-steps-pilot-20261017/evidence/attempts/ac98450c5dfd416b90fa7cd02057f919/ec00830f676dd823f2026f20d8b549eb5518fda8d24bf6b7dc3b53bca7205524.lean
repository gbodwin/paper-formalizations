import LightEFTSpanners.StoredRecordTrace
namespace LightEFTSpanners.StoredRecords.RowsStepsComparison
def rowsSteps (es : StoredSample.EdgeLists) : ℕ → Weights → ℕ :=
  fun i W => List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun r _ next i => rowSteps es i 0 r+r.length+2+next (i+1)) W i

theorem rowsSteps_nil (es : StoredSample.EdgeLists) (i : ℕ) : rowsSteps es i [] = 0 := rfl

theorem rowsSteps_cons (es : StoredSample.EdgeLists) (i : ℕ) (r : List ℚ) (rs : Weights) :
    rowsSteps es i (r::rs) = rowSteps es i 0 r+r.length+2+rowsSteps es (i+1) rs := rfl

theorem rowsSteps_eq_prior (es : StoredSample.EdgeLists) (i : ℕ) (W : Weights) :
    rowsSteps es i W = LightEFTSpanners.StoredRecords.rowsSteps es i W := by
  induction W generalizing i with
  | nil => rfl
  | cons r rs ih => exact congrArg (fun x => rowSteps es i 0 r+r.length+2+x) (ih (i+1))
#print axioms rowsSteps_eq_prior
end LightEFTSpanners.StoredRecords.RowsStepsComparison
