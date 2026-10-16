import LightEFTSpanners.StoredCandidateDrawLookup
namespace LightEFTSpanners.StoredCandidateDrawLookup.CandidateStepsComparison
def steps (key : StoredEdges.Edge) : Bank → ℕ :=
  List.rec (motive := fun _ => ℕ) 1
    (fun r _ rest => if StoredEdges.same key r.1 then 1 else 1+rest)
theorem steps_eq_prior (key : StoredEdges.Edge) (bank : Bank) :
    steps key bank = LightEFTSpanners.StoredCandidateDrawLookup.steps key bank := by
  induction bank with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨i,ds⟩
    exact congrArg (fun rest => if StoredEdges.same key i then 1 else 1+rest) ih
#print axioms steps_eq_prior
end LightEFTSpanners.StoredCandidateDrawLookup.CandidateStepsComparison
