import LightEFTSpanners.StoredRecordMachine
namespace LightEFTSpanners.StoredRecords.RowValuesComparison
def rowValues (es : StoredSample.EdgeLists) (i : ℕ) : ℕ → List ℚ → List SampleRecords.Entry :=
  fun j row => List.rec (motive := fun _ => ℕ → List SampleRecords.Entry) (fun _ => [])
    (fun w _ next j => StoredSample.entry (i,j) w es::next (j+1)) row j

theorem rowValues_nil (es : StoredSample.EdgeLists) (i j : ℕ) : rowValues es i j [] = [] := rfl

theorem rowValues_cons (es : StoredSample.EdgeLists) (i j : ℕ) (w : ℚ) (ws : List ℚ) :
    rowValues es i j (w::ws) = StoredSample.entry (i,j) w es::rowValues es i (j+1) ws := rfl

attribute [reducible] rowValues

theorem rowValues_eq_prior (es : StoredSample.EdgeLists) (i j : ℕ) (row : List ℚ) :
    rowValues es i j row = LightEFTSpanners.StoredRecords.rowValues es i j row := by
  induction row generalizing j with
  | nil => rfl
  | cons w ws ih => exact congrArg (List.cons (StoredSample.entry (i,j) w es)) (ih (j+1))
#print axioms rowValues_eq_prior
end LightEFTSpanners.StoredRecords.RowValuesComparison
