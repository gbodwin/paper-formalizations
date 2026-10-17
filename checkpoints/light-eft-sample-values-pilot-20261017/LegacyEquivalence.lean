import LightEFTSpanners.SampleRecordMatrix
namespace LightEFTSpanners.SampleRecords.ValuesComparison
open LinkedDistance
 def values : ℕ → Records → Matrix :=
  fun i records => List.rec (motive := fun _ => ℕ → Matrix) (fun _ => [])
    (fun row _ next i => rowValues i 0 row :: next (i+1)) records i

 theorem values_nil (i : ℕ) : values i [] = [] := rfl

 theorem values_cons (i : ℕ) (row : List Entry) (rows : Records) :
    values i (row::rows) = rowValues i 0 row :: values (i+1) rows := rfl

-- Preserve definitional matching in the unchanged length proof.
attribute [reducible] values


theorem values_eq_prior (i : ℕ) (records : Records) :
    values i records = LightEFTSpanners.SampleRecords.values i records := by
  induction records generalizing i with
  | nil => rfl
  | cons row rows ih => exact congrArg (List.cons (rowValues i 0 row)) (ih (i+1))
#print axioms values_eq_prior
end LightEFTSpanners.SampleRecords.ValuesComparison
