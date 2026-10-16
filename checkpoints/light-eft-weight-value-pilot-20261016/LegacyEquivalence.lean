import LightEFTSpanners.StoredOriginalWeightLookup
namespace LightEFTSpanners.StoredOriginalWeightLookup.WeightValueComparison
def value (key : StoredEdges.Edge) : Bank → ℚ :=
  List.rec (motive := fun _ => ℚ) 0
    (fun r _ rest => if StoredEdges.same key r.1 then r.2 else rest)
theorem value_eq_prior (key : StoredEdges.Edge) (bank : Bank) :
    value key bank = LightEFTSpanners.StoredOriginalWeightLookup.value key bank := by
  induction bank with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨i,q⟩
    exact congrArg (fun rest => if StoredEdges.same key i then q else rest) ih
#print axioms value_eq_prior
end LightEFTSpanners.StoredOriginalWeightLookup.WeightValueComparison
