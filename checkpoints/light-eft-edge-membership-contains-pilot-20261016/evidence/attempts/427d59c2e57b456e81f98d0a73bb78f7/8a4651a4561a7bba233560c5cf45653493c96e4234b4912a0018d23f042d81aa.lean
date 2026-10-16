import LightEFTSpanners.StoredVertexMinimum

namespace LightEFTSpanners.StoredCanonicalComponents
open StoredEdgeComponent

def least {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) : ℕ :=
  StoredVertexMinimum.value ((vertices edges root).map Fin.val) root.val

theorem least_mem {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) :
    least edges root∈(vertices edges root).map Fin.val := by
  apply StoredVertexMinimum.value_mem
  exact List.mem_map.mpr ⟨root,(mem_vertices edges root root).mpr (SimpleGraph.Reachable.refl root),rfl⟩

theorem least_lt {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) : least edges root<n := by
  obtain ⟨v,_,hv⟩ := List.mem_map.mp (least_mem edges root)
  rw [←hv]
  exact v.isLt

def representative {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) : Fin n :=
  ⟨least edges root,least_lt edges root⟩

theorem representative_reachable {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) :
    (ExecutableVoting.graph (StoredSample.edgeSet edges)).Reachable root (representative edges root) := by
  obtain ⟨v,hv,he⟩ := List.mem_map.mp (least_mem edges root)
  have h : v=representative edges root := Fin.ext he
  rw [←h]
  exact (mem_vertices edges root v).mp hv

theorem representative_le {n : ℕ} (edges : List (Fin n × Fin n)) (root v : Fin n)
    (hv : (ExecutableVoting.graph (StoredSample.edgeSet edges)).Reachable root v) :
    representative edges root≤v := by
  apply StoredVertexMinimum.value_le_mem
  exact List.mem_map.mpr ⟨v,(mem_vertices edges root v).mpr hv,rfl⟩

theorem representative_eq {n : ℕ} (edges : List (Fin n × Fin n)) (u v : Fin n)
    (h : (ExecutableVoting.graph (StoredSample.edgeSet edges)).Reachable u v) :
    representative edges u=representative edges v := by
  apply le_antisymm
  · exact representative_le edges u _ (h.trans (representative_reachable edges v))
  · exact representative_le edges v _ (h.symm.trans (representative_reachable edges u))

theorem representative_fixed {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) :
    representative edges (representative edges root)=representative edges root :=
  (representative_eq edges root _ (representative_reachable edges root)).symm

def roots {n : ℕ} (edges : List (Fin n × Fin n)) : List (Fin n) :=
  (List.finRange n).filter fun root => decide (representative edges root=root)

theorem roots_nodup {n : ℕ} (edges : List (Fin n × Fin n)) : (roots edges).Nodup :=
  (List.nodup_finRange n).filter _

theorem mem_roots {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) :
    root∈roots edges ↔ representative edges root=root := by simp [roots]

theorem exists_unique_root {n : ℕ} (edges : List (Fin n × Fin n)) (v : Fin n) :
    ∃! root,root∈roots edges ∧ (ExecutableVoting.graph (StoredSample.edgeSet edges)).Reachable v root := by
  refine ⟨representative edges v,⟨(mem_roots edges _).mpr (representative_fixed edges v),
    representative_reachable edges v⟩,?_⟩
  intro root h
  rw [←(mem_roots edges root).mp h.1]
  exact (representative_eq edges v root h.2).symm
end LightEFTSpanners.StoredCanonicalComponents
