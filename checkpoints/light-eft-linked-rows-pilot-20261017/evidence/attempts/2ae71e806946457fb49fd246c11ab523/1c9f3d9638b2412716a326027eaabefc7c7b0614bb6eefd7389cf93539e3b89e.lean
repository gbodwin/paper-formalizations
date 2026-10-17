import LightEFTSpanners.LinkedDistanceKernel
namespace LightEFTSpanners.LinkedDistance.RowsComparison
def rows (d : List Cell) : Matrix → List Cell → List Cell :=
  fun rs => List.rec (motive := fun _ => List Cell → List Cell) (fun _ => [])
    (fun r _ next ds => match ds with
      | [] => []
      | a::as => scan r d a :: next as) rs

theorem rows_nil (d ds : List Cell) : rows d [] ds = [] := rfl

theorem rows_cons_nil (d r : List Cell) (rs : Matrix) : rows d (r::rs) [] = [] := rfl

theorem rows_cons_cons (d r : List Cell) (rs : Matrix) (a : Cell) (as : List Cell) :
    rows d (r::rs) (a::as) = scan r d a :: rows d rs as := rfl

-- Preserve definitional matching in the unchanged length and trace proofs.
attribute [reducible] rows


theorem rows_eq_prior (d : List Cell) (rs : Matrix) (ds : List Cell) :
    rows d rs ds = LightEFTSpanners.LinkedDistance.rows d rs ds := by
  induction rs generalizing ds with
  | nil => rfl
  | cons r rs ih =>
    cases ds with
    | nil => rfl
    | cons a as => exact congrArg (List.cons (scan r d a)) (ih as)
#print axioms rows_eq_prior
end LightEFTSpanners.LinkedDistance.RowsComparison
