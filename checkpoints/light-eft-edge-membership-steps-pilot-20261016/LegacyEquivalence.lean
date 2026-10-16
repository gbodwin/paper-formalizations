import LightEFTSpanners.StoredEdgeMembership
namespace LightEFTSpanners.StoredEdges.StepsComparison
def steps (q : Edge) : List Edge → ℕ :=
  List.rec (motive := fun _ => ℕ) 1
    (fun e _ rest => if same q e then 1 else rest+1)
theorem steps_eq_prior (q : Edge) (es : List Edge) :
    steps q es = LightEFTSpanners.StoredEdges.steps q es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    exact congrArg (fun rest => if same q e then 1 else rest+1) ih
#print axioms steps_eq_prior
end LightEFTSpanners.StoredEdges.StepsComparison
