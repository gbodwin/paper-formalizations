import LightEFTSpanners.LinkedDistanceTrace
namespace LightEFTSpanners.LinkedDistance.RowTicksComparison
 def rowTicks (d : List Cell) : Matrix → List Cell → ℕ :=
  fun rs => List.rec (motive := fun _ => List Cell → ℕ) (fun _ => 0)
    (fun r _ next ds => match ds with
      | [] => 0
      | _::as => min r.length d.length+3+next as) rs

 theorem rowTicks_nil (d ds : List Cell) : rowTicks d [] ds = 0 := rfl

 theorem rowTicks_cons_nil (d r : List Cell) (rs : Matrix) :
    rowTicks d (r::rs) [] = 0 := rfl

 theorem rowTicks_cons_cons (d r : List Cell) (rs : Matrix) (a : Cell) (as : List Cell) :
    rowTicks d (r::rs) (a::as) = min r.length d.length+3+rowTicks d rs as := rfl

-- Preserve definitional matching in the unchanged trace and arithmetic proofs.
attribute [reducible] rowTicks


theorem rowTicks_eq_prior (d : List Cell) (rs : Matrix) (ds : List Cell) :
    rowTicks d rs ds = LightEFTSpanners.LinkedDistance.rowTicks d rs ds := by
  induction rs generalizing ds with
  | nil => rfl
  | cons r rs ih =>
    cases ds with
    | nil => rfl
    | cons a as => exact congrArg (fun n => min r.length d.length+3+n) (ih as)
#print axioms rowTicks_eq_prior
end LightEFTSpanners.LinkedDistance.RowTicksComparison
