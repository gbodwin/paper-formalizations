import LightEFTSpanners.StoredDrawLookup
namespace LightEFTSpanners.StoredDrawLookup.ValueComparison
def value (key : ℕ) : Bank → StoredVote.Draws :=
  List.rec (motive := fun _ => StoredVote.Draws) []
    (fun r _ rest => if key=r.1 then r.2 else rest)
theorem value_eq_prior (key : ℕ) (bank : Bank) :
    value key bank = LightEFTSpanners.StoredDrawLookup.value key bank := by
  induction bank with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨i,ds⟩
    exact congrArg (fun rest => if key=i then ds else rest) ih
#print axioms value_eq_prior
end LightEFTSpanners.StoredDrawLookup.ValueComparison
