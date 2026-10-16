import LightEFTSpanners.StoredDrawLookup
namespace LightEFTSpanners.StoredDrawLookup.StepsComparison
def steps (key : ℕ) : Bank → ℕ :=
  List.rec (motive := fun _ => ℕ) 1
    (fun r _ rest => if key=r.1 then 1 else 1+rest)
theorem steps_eq_prior (key : ℕ) (bank : Bank) :
    steps key bank = LightEFTSpanners.StoredDrawLookup.steps key bank := by
  induction bank with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨i,ds⟩
    exact congrArg (fun rest => if key=i then 1 else 1+rest) ih
#print axioms steps_eq_prior
end LightEFTSpanners.StoredDrawLookup.StepsComparison
