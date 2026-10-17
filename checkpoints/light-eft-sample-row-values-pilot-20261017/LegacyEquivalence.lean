import LightEFTSpanners.SampleRecordMatrix
namespace LightEFTSpanners.SampleRecords.RowValuesComparison
open LinkedDistance
 def rowValues (i : ℕ) : ℕ → List Entry → List Cell :=
  fun j entries => List.rec (motive := fun _ => ℕ → List Cell) (fun _ => [])
    (fun a _ next j => value i j a :: next (j+1)) entries j

 theorem rowValues_nil (i j : ℕ) : rowValues i j [] = [] := rfl

 theorem rowValues_cons (i j : ℕ) (a : Entry) (as : List Entry) :
    rowValues i j (a::as) = value i j a :: rowValues i (j+1) as := rfl

-- Preserve definitional matching in the unchanged length proof.
attribute [reducible] rowValues


theorem rowValues_eq_prior (i j : ℕ) (entries : List Entry) :
    rowValues i j entries = LightEFTSpanners.SampleRecords.rowValues i j entries := by
  induction entries generalizing j with
  | nil => rfl
  | cons a as ih => exact congrArg (List.cons (value i j a)) (ih (j+1))
#print axioms rowValues_eq_prior
end LightEFTSpanners.SampleRecords.RowValuesComparison
