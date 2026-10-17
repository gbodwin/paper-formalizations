import LightEFTSpanners.StoredRecordMachine
namespace LightEFTSpanners.StoredRecords.ValuesComparison
def values (es : StoredSample.EdgeLists) : ℕ → Weights → SampleRecords.Records :=
  fun i rows => List.rec (motive := fun _ => ℕ → SampleRecords.Records) (fun _ => [])
    (fun row _ next i => rowValues es i 0 row::next (i+1)) rows i

theorem values_nil (es : StoredSample.EdgeLists) (i : ℕ) : values es i [] = [] := rfl

theorem values_cons (es : StoredSample.EdgeLists) (i : ℕ) (row : List ℚ) (rows : Weights) :
    values es i (row::rows) = rowValues es i 0 row::values es (i+1) rows := rfl

-- Preserve definitional matching in the unchanged length proof.
attribute [reducible] values


theorem values_eq_prior (es : StoredSample.EdgeLists) (i : ℕ) (rows : Weights) :
    values es i rows = LightEFTSpanners.StoredRecords.values es i rows := by
  induction rows generalizing i with
  | nil => rfl
  | cons row rows ih => exact congrArg (List.cons (rowValues es i 0 row)) (ih (i+1))
#print axioms values_eq_prior
end LightEFTSpanners.StoredRecords.ValuesComparison
