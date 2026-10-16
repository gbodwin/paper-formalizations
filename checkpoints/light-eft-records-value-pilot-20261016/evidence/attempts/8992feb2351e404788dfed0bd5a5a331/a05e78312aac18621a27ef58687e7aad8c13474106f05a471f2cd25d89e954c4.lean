import LightEFTSpanners.StoredOriginalCandidateRecords
namespace LightEFTSpanners.StoredOriginalCandidateRecords.RecordsValueComparison
def value (Q : List StoredEdges.Edge) (bank : StoredCandidateDrawLookup.Bank) :
    List StoredEdges.Edge → List StoredForestBank.Input :=
  List.rec (motive := fun _ => List StoredForestBank.Input) []
    (fun x _ rest => if StoredEdges.contains x Q then rest
      else ⟨x,StoredCandidateDrawLookup.value x bank⟩::rest)
theorem value_eq_prior (Q : List StoredEdges.Edge) (bank : StoredCandidateDrawLookup.Bank)
    (xs : List StoredEdges.Edge) :
    value Q bank xs = LightEFTSpanners.StoredOriginalCandidateRecords.value Q bank xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    exact congrArg (fun rest => if StoredEdges.contains x Q then rest
      else (⟨x,StoredCandidateDrawLookup.value x bank⟩ : StoredForestBank.Input)::rest) ih
#print axioms value_eq_prior
end LightEFTSpanners.StoredOriginalCandidateRecords.RecordsValueComparison
