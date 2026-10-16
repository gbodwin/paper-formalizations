import LightEFTSpanners.StoredFlagSample
namespace LightEFTSpanners.StoredFlagSample.ValuePilotComparison
def value : Input → List StoredEdges.Edge :=
  List.rec (motive := fun _ => List StoredEdges.Edge) []
    (fun x _ rest => if x.2 then x.1::rest else rest)
theorem value_eq_prior (xs : Input) :
    value xs = LightEFTSpanners.StoredFlagSample.value xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨e,b⟩
    cases b with
    | false => exact ih
    | true => exact congrArg (List.cons e) ih
#print axioms value_eq_prior
end LightEFTSpanners.StoredFlagSample.ValuePilotComparison
