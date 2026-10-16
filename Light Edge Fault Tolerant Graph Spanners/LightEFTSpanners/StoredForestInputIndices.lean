import LightEFTSpanners.StoredCanonicalComponentRoot

namespace LightEFTSpanners.StoredForestInput
attribute [local instance] Classical.propDecidable

def rootRecord {n : ℕ} (bank : StoredDrawLookup.TypedBank n) (i : ℕ)
    (es : List (Fin n × Fin n)) (root : Fin n) : StoredComponentRecord.TypedInput n :=
  ⟨StoredForestHosts.label n i root.val,StoredEdgeComponent.vertices es root,
    ⟨StoredDiscoveredHosts.typedHost es root,
      StoredDrawLookup.typedValue (StoredForestHosts.label n i root.val) bank⟩⟩

noncomputable def componentRecord {n : ℕ} (bank : StoredDrawLookup.TypedBank n) (i : ℕ)
    (es : List (Fin n × Fin n))
    (c : (ExecutableVoting.graph (StoredSample.edgeSet es)).ConnectedComponent) : StoredComponentRecord.TypedInput n :=
  rootRecord bank i es (StoredCanonicalComponents.componentRoot es c)

theorem component_records {n : ℕ} (bank : StoredDrawLookup.TypedBank n) (i : ℕ)
    (es : List (Fin n × Fin n)) :
    (StoredCanonicalComponents.indices es).map (componentRecord bank i es)=
      (StoredCanonicalComponents.roots es).map (rootRecord bank i es) := by
  simp only [StoredCanonicalComponents.indices,List.map_map]
  apply List.map_congr_left
  intro root hr
  simp only [Function.comp_apply,componentRecord,StoredCanonicalComponents.componentRoot_mk es root hr]

theorem typedInputs_ofFn {n q : ℕ} (bank : StoredDrawLookup.TypedBank n) (i : ℕ)
    (edges : Fin q → List (Fin n × Fin n)) :
    typedInputs bank i (List.ofFn edges)=
      (List.finRange q).flatMap (fun j => (StoredCanonicalComponents.roots (edges j)).map
        (rootRecord bank (i+j.val) (edges j))) := by
  induction q generalizing i with
  | zero => simp [typedInputs]
  | succ q ih =>
    rw [List.ofFn_succ,List.finRange_succ]
    simp only [typedInputs_cons,List.flatMap_cons,List.flatMap_map]
    rw [ih]
    simp [rootRecord,Nat.add_comm,Nat.add_left_comm]
end LightEFTSpanners.StoredForestInput
