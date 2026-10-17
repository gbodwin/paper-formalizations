import LightEFTSpanners.StoredCanonicalExecutable

namespace LightEFTSpanners.StoredCanonicalEnumeration
open StoredCanonicalComponents

def records {n : ℕ} (edges : List (Fin n × Fin n)) : List Record :=
  (roots edges).map fun root => (root.val,(StoredEdgeComponent.vertices edges root).map Fin.val)

theorem values_eq {n : ℕ} (edges : List (Fin n × Fin n)) (rs : List (Fin n)) :
    values edges rs=(rs.filter fun r => decide (representative edges r=r)).map
      (fun root => (root.val,(StoredEdgeComponent.vertices edges root).map Fin.val)) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    by_cases hr : representative edges r=r
    · have h : least edges r=r.val := congrArg Fin.val hr
      simp [values,StoredCanonicalRoot.result,h,hr]
      simpa [values,StoredCanonicalRoot.result] using ih
    · have h : least edges r≠r.val := fun he => hr (Fin.ext he)
      simp [values,StoredCanonicalRoot.result,h,hr]
      simpa [values,StoredCanonicalRoot.result] using ih

theorem execute_records {n : ℕ} (edges : List (Fin n × Fin n)) :
    execute n (StoredEdges.encode edges)=records edges := by
  rw [execute_eq,values_eq]
  rfl

theorem mem_records {n : ℕ} (edges : List (Fin n × Fin n)) (r : ℕ) (vs : List ℕ) :
    (r,vs)∈records edges ↔ ∃ root : Fin n,root∈roots edges ∧ root.val=r ∧
      vs=(StoredEdgeComponent.vertices edges root).map Fin.val := by
  simp only [records,List.mem_map,Prod.mk.injEq]
  constructor
  · rintro ⟨root,hr,h₁,h₂⟩
    exact ⟨root,hr,h₁,h₂.symm⟩
  · rintro ⟨root,hr,h₁,h₂⟩
    exact ⟨root,hr,h₁,h₂.symm⟩

theorem component_cover {n : ℕ} (edges : List (Fin n × Fin n)) (v : Fin n) :
    ∃ root : Fin n,∃ vs,(root.val,vs)∈execute n (StoredEdges.encode edges) ∧ v.val∈vs := by
  obtain ⟨root,⟨hr,hreach⟩,_⟩ := exists_unique_root edges v
  refine ⟨root,(StoredEdgeComponent.vertices edges root).map Fin.val,?_,?_⟩
  · rw [execute_records,mem_records]
    exact ⟨root,hr,rfl,rfl⟩
  · exact List.mem_map.mpr ⟨v,(StoredEdgeComponent.mem_vertices edges root v).mpr hreach.symm,rfl⟩

theorem component_disjoint {n : ℕ} (edges : List (Fin n × Fin n)) (r s : ℕ) (xs ys : List ℕ)
    (hx : (r,xs)∈execute n (StoredEdges.encode edges))
    (hy : (s,ys)∈execute n (StoredEdges.encode edges)) (v : ℕ) (hvx : v∈xs) (hvy : v∈ys) : r=s := by
  rw [execute_records,mem_records] at hx hy
  obtain ⟨root,hr,rfl,rfl⟩ := hx
  obtain ⟨other,ho,rfl,rfl⟩ := hy
  obtain ⟨x,hx,hxv⟩ := List.mem_map.mp hvx
  obtain ⟨y,hy,hyv⟩ := List.mem_map.mp hvy
  have hxy : x=y := Fin.ext (hxv.trans hyv.symm)
  subst y
  have hreach := ((StoredEdgeComponent.mem_vertices edges root x).mp hx).trans
    ((StoredEdgeComponent.mem_vertices edges other x).mp hy).symm
  have he := representative_eq edges root other hreach
  rw [(mem_roots edges root).mp hr,(mem_roots edges other).mp ho] at he
  exact congrArg Fin.val he

theorem records_nodup {n : ℕ} (edges : List (Fin n × Fin n)) : (records edges).Nodup := by
  apply (roots_nodup edges).map
  intro a b h
  exact Fin.ext (congrArg Prod.fst h)

theorem root_mem_record {n : ℕ} (edges : List (Fin n × Fin n)) (r : ℕ) (vs : List ℕ)
    (h : (r,vs)∈execute n (StoredEdges.encode edges)) : r∈vs := by
  rw [execute_records,mem_records] at h
  obtain ⟨root,_,rfl,rfl⟩ := h
  exact List.mem_map.mpr ⟨root,(StoredEdgeComponent.mem_vertices edges root root).mpr
    (SimpleGraph.Reachable.refl root),rfl⟩
end LightEFTSpanners.StoredCanonicalEnumeration
