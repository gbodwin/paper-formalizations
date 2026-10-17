import LightEFTSpanners.StoredRecordMachine
namespace LightEFTSpanners.StoredRecords.RowStepsComparison
def rowSteps (es : StoredSample.EdgeLists) (i : ℕ) : ℕ → List ℚ → ℕ :=
  fun j row => List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1)
    (fun _ _ next j => StoredSample.entrySteps (i,j) es+2+next (j+1)) row j

theorem rowSteps_nil (es : StoredSample.EdgeLists) (i j : ℕ) : rowSteps es i j [] = 1 := rfl

theorem rowSteps_cons (es : StoredSample.EdgeLists) (i j : ℕ) (w : ℚ) (ws : List ℚ) :
    rowSteps es i j (w::ws) = StoredSample.entrySteps (i,j) es+2+rowSteps es i (j+1) ws := rfl

-- Let arithmetic normalization identify the exact unfolded tail count.
attribute [reducible] rowSteps

theorem rowSteps_eq_prior (es : StoredSample.EdgeLists) (i j : ℕ) (row : List ℚ) :
    rowSteps es i j row = LightEFTSpanners.StoredRecords.rowSteps es i j row := by
  induction row generalizing j with
  | nil => rfl
  | cons w ws ih => exact congrArg (fun x => StoredSample.entrySteps (i,j) es+2+x) (ih (j+1))
#print axioms rowSteps_eq_prior
end LightEFTSpanners.StoredRecords.RowStepsComparison
