import LightEFTSpanners.StoredDrawLookupEncoding
namespace LightEFTSpanners.StoredForestInput.InputsPilotComparison
def typedInputs {n : ℕ} (bank : StoredDrawLookup.TypedBank n) :
    ℕ → List (List (Fin n × Fin n)) → List (StoredComponentRecord.TypedInput n) :=
  fun i fs => List.rec (motive := fun _ => ℕ → List (StoredComponentRecord.TypedInput n))
    (fun _ => [])
    (fun es _ next j => (StoredCanonicalComponents.roots es).map (fun root =>
      ⟨StoredForestHosts.label n j root.val,StoredEdgeComponent.vertices es root,
        ⟨StoredDiscoveredHosts.typedHost es root,
          StoredDrawLookup.typedValue (StoredForestHosts.label n j root.val) bank⟩⟩) ++ next (j+1)) fs i
theorem typedInputs_eq_prior {n : ℕ} (bank : StoredDrawLookup.TypedBank n)
    (i : ℕ) (fs : List (List (Fin n × Fin n))) :
    typedInputs bank i fs = LightEFTSpanners.StoredForestInput.typedInputs bank i fs := by
  induction fs generalizing i with
  | nil => rfl
  | cons es fs ih =>
    exact congrArg (fun tail => (StoredCanonicalComponents.roots es).map (fun root =>
      (⟨StoredForestHosts.label n i root.val,StoredEdgeComponent.vertices es root,
        ⟨StoredDiscoveredHosts.typedHost es root,
          StoredDrawLookup.typedValue (StoredForestHosts.label n i root.val) bank⟩⟩ : StoredComponentRecord.TypedInput n)) ++ tail) (ih (i+1))
#print axioms typedInputs_eq_prior
end LightEFTSpanners.StoredForestInput.InputsPilotComparison
