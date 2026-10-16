import LightEFTSpanners.StoredAssignmentDrawList

namespace LightEFTSpanners.StoredDrawLookup

theorem typedValue_indexed {n : ℕ} {J : Type*} (id : J → ℕ) (hid : Function.Injective id)
    (draws : J → List (List (Fin n × Fin n))) (js : List J) (j : J) (hj : j∈js) :
    typedValue (id j) (js.map fun x => (id x,draws x))=draws j := by
  induction js with
  | nil => simp at hj
  | cons i js ih =>
    by_cases he : j=i
    · subst i
      simp [typedValue]
    · have hn : id j≠id i := fun h => he (hid h)
      simp only [List.map_cons,typedValue,hn,↓reduceIte]
      exact ih ((List.mem_cons.mp hj).resolve_left he)
end LightEFTSpanners.StoredDrawLookup

namespace LightEFTSpanners.StoredForestCandidates
attribute [local instance] Classical.propDecidable

noncomputable def assignmentBank {n q m : ℕ} (edges : Fin q → List (Fin n × Fin n))
    (a : SampledGreedy.Assignment (Fin n) (ForestComponentIndex (StoredForestHosts.family edges)) m)
    (e : Sym2 (Fin n)) : StoredDrawLookup.TypedBank n :=
  (StoredForestHosts.indices edges).map fun j =>
    (componentId edges j,(List.ofFn (a e j)).map setEdges)

theorem assignmentBank_lookup {n q m : ℕ} (edges : Fin q → List (Fin n × Fin n))
    (a : SampledGreedy.Assignment (Fin n) (ForestComponentIndex (StoredForestHosts.family edges)) m)
    (e : Sym2 (Fin n)) (j : ForestComponentIndex (StoredForestHosts.family edges)) :
    StoredDrawLookup.typedValue (componentId edges j) (assignmentBank edges a e)=
      (List.ofFn (a e j)).map setEdges :=
  StoredDrawLookup.typedValue_indexed (componentId edges) (componentId_injective edges)
    (fun j => (List.ofFn (a e j)).map setEdges) (StoredForestHosts.indices edges) j
    (StoredForestHosts.indices_all edges j)

theorem assignmentBank_represents {n q m : ℕ} (edges : Fin q → List (Fin n × Fin n))
    (a : SampledGreedy.Assignment (Fin n) (ForestComponentIndex (StoredForestHosts.family edges)) m)
    (e : Sym2 (Fin n)) (j : ForestComponentIndex (StoredForestHosts.family edges)) :
    ((hostInput edges (assignmentBank edges a) e j).draws.map StoredSample.edgeSet)=List.ofFn (a e j) := by
  change (StoredDrawLookup.typedValue (componentId edges j) (assignmentBank edges a e)).map StoredSample.edgeSet=_
  rw [assignmentBank_lookup,List.map_map]
  simp only [Function.comp_def,setEdges_represents]
  exact List.map_id _
end LightEFTSpanners.StoredForestCandidates
