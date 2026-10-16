import LightEFTSpanners.StoredCandidateDrawEncoding
namespace LightEFTSpanners.StoredOriginalCandidateRecords.RecordsPilotComparison
def typedValue {n : ℕ} (Q : List (Fin n × Fin n)) (bank : StoredCandidateDrawLookup.TypedBank n) :
    List (Fin n × Fin n) → List (StoredForestBank.TypedInput n) :=
  List.rec (motive := fun _ => List (StoredForestBank.TypedInput n)) []
    (fun x _ rest => if s(x.1,x.2)∈StoredSample.edgeSet Q then rest
      else ⟨x,StoredCandidateDrawLookup.typedValue s(x.1,x.2) bank⟩::rest)
theorem typedValue_eq_prior {n : ℕ} (Q : List (Fin n × Fin n))
    (bank : StoredCandidateDrawLookup.TypedBank n) (xs : List (Fin n × Fin n)) :
    typedValue Q bank xs = LightEFTSpanners.StoredOriginalCandidateRecords.typedValue Q bank xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    exact congrArg (fun rest => if s(x.1,x.2)∈StoredSample.edgeSet Q then rest
      else (⟨x,StoredCandidateDrawLookup.typedValue s(x.1,x.2) bank⟩ : StoredForestBank.TypedInput n)::rest) ih
#print axioms typedValue_eq_prior
end LightEFTSpanners.StoredOriginalCandidateRecords.RecordsPilotComparison
