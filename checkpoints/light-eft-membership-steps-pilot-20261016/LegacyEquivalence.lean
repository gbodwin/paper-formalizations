import LightEFTSpanners.StoredVertexMembership
namespace LightEFTSpanners.StoredVertexMembership.StepsComparison
def steps (v : ℕ) : List ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ) 1
    (fun x _ rest => if v=x then 1 else rest+1)
theorem steps_eq_prior (v : ℕ) (xs : List ℕ) :
    steps v xs = LightEFTSpanners.StoredVertexMembership.steps v xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    exact congrArg (fun rest => if v=x then 1 else rest+1) ih
#print axioms steps_eq_prior
end LightEFTSpanners.StoredVertexMembership.StepsComparison
