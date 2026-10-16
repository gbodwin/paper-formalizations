import LightEFTSpanners.StoredForestAssignment

namespace LightEFTSpanners.StoredForestCandidates
attribute [local instance] Classical.propDecidable

noncomputable def setEdges {n : ℕ} (S : Finset (Sym2 (Fin n))) : List (Fin n × Fin n) :=
  S.toList.map fun e => e.out

theorem setEdges_represents {n : ℕ} (S : Finset (Sym2 (Fin n))) :
    StoredSample.edgeSet (setEdges S)=S := by
  unfold StoredSample.edgeSet setEdges
  rw [List.map_map]
  have he : (S.toList.map fun e => s(e.out.1,e.out.2))=S.toList := by
    conv_rhs => rw [←List.map_id S.toList]
    apply List.map_congr_left
    intro e _
    exact e.out_eq
  simpa only [Function.comp_def,he] using S.toList_toFinset

theorem componentId_injective {n q : ℕ} (edges : Fin q → List (Fin n × Fin n)) :
    Function.Injective (componentId edges) := by
  intro j k he
  rcases j with ⟨i,c⟩
  rcases k with ⟨l,d⟩
  change StoredForestHosts.label n i.val (StoredCanonicalComponents.componentRoot (edges i) c).val=
    StoredForestHosts.label n l.val (StoredCanonicalComponents.componentRoot (edges l) d).val at he
  obtain ⟨hi,hr⟩ := StoredForestHosts.label_injective
    (StoredCanonicalComponents.componentRoot (edges i) c).isLt
    (StoredCanonicalComponents.componentRoot (edges l) d).isLt he
  have hil : i=l := Fin.ext hi
  subst l
  have hroot := Fin.ext hr
  have hc := StoredCanonicalComponents.componentRoot_eq (edges i) c
  have hd := StoredCanonicalComponents.componentRoot_eq (edges i) d
  have hcd : c=d := hc.symm.trans ((congrArg
    (ExecutableVoting.graph (StoredSample.edgeSet (edges i))).connectedComponentMk hroot).trans hd)
  subst d
  rfl
end LightEFTSpanners.StoredForestCandidates
