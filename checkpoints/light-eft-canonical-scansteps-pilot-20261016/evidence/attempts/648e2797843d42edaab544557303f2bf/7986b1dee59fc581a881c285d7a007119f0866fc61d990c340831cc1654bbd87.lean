import LightEFTSpanners.StoredForestComponentIndices

namespace LightEFTSpanners.StoredForestHosts

theorem mem_execute_family {n q : ℕ} (edges : Fin q → List (Fin n × Fin n)) (r : Record) :
    r∈execute n ((List.ofFn edges).map StoredEdges.encode) ↔
      ∃ i : Fin q,∃ root : Fin n,root∈StoredCanonicalComponents.roots (edges i) ∧
        r=(i.val,componentRecord (edges i) root) := by
  rw [execute_eq,mem_value]
  constructor
  · rintro ⟨j,es,root,hj,hr,he⟩
    by_cases h : j<q
    · have hes : edges ⟨j,h⟩=es := by simpa [List.getElem?_ofFn,h] using hj
      subst es
      exact ⟨⟨j,h⟩,root,hr,by simpa using he⟩
    · simp [h] at hj
  · rintro ⟨i,root,hr,he⟩
    exact ⟨i.val,edges i,root,by simp [i.isLt],hr,by simpa using he⟩

theorem component_coverage {n q : ℕ} (edges : Fin q → List (Fin n × Fin n))
    (j : ForestComponentIndex (family edges)) :
    ∃ root : Fin n,(j.1.val,componentRecord (edges j.1) root)∈
      execute n ((List.ofFn edges).map StoredEdges.encode) ∧
      (family edges j.1).connectedComponentMk root=j.2 := by
  have h := StoredCanonicalComponents.indices_all (edges j.1) j.2
  obtain ⟨root,hr,he⟩ := List.mem_map.mp h
  refine ⟨root,?_,he⟩
  exact (mem_execute_family edges _).mpr ⟨j.1,root,hr,rfl⟩
end LightEFTSpanners.StoredForestHosts
