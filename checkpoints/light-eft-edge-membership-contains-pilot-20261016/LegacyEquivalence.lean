import LightEFTSpanners.StoredEdgeMembership
namespace LightEFTSpanners.StoredEdges.ContainsComparison
def contains (q : Edge) : List Edge → Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun e _ rest => if same q e then true else rest)
theorem contains_eq_prior (q : Edge) (es : List Edge) :
    contains q es = LightEFTSpanners.StoredEdges.contains q es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    exact congrArg (fun rest => if same q e then true else rest) ih
#print axioms contains_eq_prior
end LightEFTSpanners.StoredEdges.ContainsComparison
