import LightEFTSpanners.StoredCandidateDrawLookup
namespace LightEFTSpanners.StoredCandidateDrawLookup.CandidateValueComparison
def value (key : StoredEdges.Edge) : Bank → StoredDrawLookup.Bank :=
  List.rec (motive := fun _ => StoredDrawLookup.Bank) []
    (fun r _ rest => if StoredEdges.same key r.1 then r.2 else rest)
theorem value_eq_prior (key : StoredEdges.Edge) (bank : Bank) :
    value key bank = LightEFTSpanners.StoredCandidateDrawLookup.value key bank := by
  induction bank with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨i,ds⟩
    exact congrArg (fun rest => if StoredEdges.same key i then ds else rest) ih
#print axioms value_eq_prior
end LightEFTSpanners.StoredCandidateDrawLookup.CandidateValueComparison
