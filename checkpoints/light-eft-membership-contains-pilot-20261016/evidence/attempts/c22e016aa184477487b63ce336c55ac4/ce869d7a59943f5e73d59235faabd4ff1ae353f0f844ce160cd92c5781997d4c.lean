import LightEFTSpanners.StoredVertexMembership
namespace LightEFTSpanners.StoredVertexMembership.ContainsComparison
def contains (v : ℕ) : List ℕ → Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun x _ rest => if v=x then true else rest)
theorem contains_eq_prior (v : ℕ) (xs : List ℕ) :
    contains v xs = LightEFTSpanners.StoredVertexMembership.contains v xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    exact congrArg (fun rest => if v=x then true else rest) ih
#print axioms contains_eq_prior
end LightEFTSpanners.StoredVertexMembership.ContainsComparison
