import LightEFTSpanners.StoredComponentHostTrace

namespace LightEFTSpanners.StoredComponentHostFilter

def typedValue {n : ℕ} (vs : List (Fin n)) (edges : List (Fin n × Fin n)) : List (Fin n × Fin n) :=
  edges.filter fun e => decide (e.1≠e.2 ∧ e.1∈vs ∧ e.2∈vs)

theorem contains_encoded {n : ℕ} (v : Fin n) (vs : List (Fin n)) :
    StoredVertexMembership.contains v.val (vs.map Fin.val)=decide (v∈vs) := by
  apply Bool.eq_iff_iff.mpr
  rw [StoredVertexMembership.contains_iff,decide_eq_true_eq]
  constructor
  · intro hmem
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hmem
    have h : x=v := Fin.ext he
    simpa only [←h] using hx
  · intro h
    exact List.mem_map.mpr ⟨v,h,rfl⟩

theorem selected_encoded {n : ℕ} (u v : Fin n) (vs : List (Fin n)) :
    selected (vs.map Fin.val) (u.val,v.val)=decide (u≠v ∧ u∈vs ∧ v∈vs) := by
  simp [selected,contains_encoded,Fin.ext_iff,Bool.and_assoc]

theorem value_encoded {n : ℕ} (vs : List (Fin n)) (edges : List (Fin n × Fin n)) :
    value (vs.map Fin.val) (StoredEdges.encode edges)=StoredEdges.encode (typedValue vs edges) := by
  unfold value StoredEdges.encode typedValue
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro e _
  exact selected_encoded e.1 e.2 vs

theorem mem_host_iff {n : ℕ} (vs : List (Fin n)) (edges : List (Fin n × Fin n)) (u v : Fin n) :
    s(u,v)∈StoredSample.edgeSet (typedValue vs edges) ↔
      u≠v ∧ u∈vs ∧ v∈vs ∧ s(u,v)∈StoredSample.edgeSet edges := by
  simp only [StoredSample.edgeSet,List.mem_toFinset,List.mem_map]
  constructor
  · rintro ⟨⟨a,b⟩,he,hpair⟩
    obtain ⟨hm,hcond⟩ := List.mem_filter.mp he
    obtain ⟨hab,hav,hbv⟩ := of_decide_eq_true hcond
    rcases Sym2.eq_iff.mp hpair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hab,hav,hbv,⟨(a,b),hm,rfl⟩⟩
    · exact ⟨Ne.symm hab,hbv,hav,⟨(a,b),hm,Sym2.eq_swap⟩⟩
  · rintro ⟨huv,hu,hv,⟨⟨a,b⟩,hm,hpair⟩⟩
    rcases Sym2.eq_iff.mp hpair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨(a,b),List.mem_filter.mpr ⟨hm,by simpa using And.intro huv (And.intro hu hv)⟩,rfl⟩
    · exact ⟨(a,b),List.mem_filter.mpr ⟨hm,by simpa using And.intro (Ne.symm huv) (And.intro hv hu)⟩,Sym2.eq_swap⟩
end LightEFTSpanners.StoredComponentHostFilter
