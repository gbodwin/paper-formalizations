import LightEFTSpanners.StoredForestHostsExecutable

namespace LightEFTSpanners.StoredForestHosts

def componentRecord {n : ℕ} (es : List (Fin n × Fin n)) (root : Fin n) : StoredCanonicalHosts.Record :=
  ((root.val,(StoredEdgeComponent.vertices es root).map Fin.val),
    StoredEdges.encode (StoredDiscoveredHosts.typedHost es root))

theorem mem_value {n : ℕ} (fs : List (List (Fin n × Fin n))) (i : ℕ) (r : Record) :
    r∈value i fs ↔ ∃ j es,∃ root : Fin n,fs[j]?=some es ∧
      root∈StoredCanonicalComponents.roots es ∧ r=(i+j,componentRecord es root) := by
  induction fs generalizing i with
  | nil => simp [value]
  | cons es fs ih =>
    constructor
    · intro h
      rw [value,List.mem_append] at h
      rcases h with h|h
      · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp h
        rw [StoredDiscoveredHosts.value_original] at hc
        obtain ⟨root,hr,rfl⟩ := List.mem_map.mp hc
        exact ⟨0,es,root,rfl,hr,by simp [componentRecord]⟩
      · obtain ⟨j,es',root,hj,hr,he⟩ := (ih (i+1)).mp h
        exact ⟨j+1,es',root,by simpa using hj,hr,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he⟩
    · rintro ⟨j,es',root,hj,hr,he⟩
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at hj
        subst es'
        rw [he,value,List.mem_append]
        apply Or.inl
        apply List.mem_map.mpr
        refine ⟨componentRecord es root,?_,by simp⟩
        rw [StoredDiscoveredHosts.value_original]
        exact List.mem_map.mpr ⟨root,hr,rfl⟩
      | succ j =>
        rw [value,List.mem_append]
        apply Or.inr
        apply (ih (i+1)).mpr
        exact ⟨j,es',root,by simpa using hj,hr,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he⟩
end LightEFTSpanners.StoredForestHosts
