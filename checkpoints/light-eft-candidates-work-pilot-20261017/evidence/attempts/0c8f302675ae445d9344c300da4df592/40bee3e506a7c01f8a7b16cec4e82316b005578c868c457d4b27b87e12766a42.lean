import LightEFTSpanners.StoredVertexPairs
import LightEFTSpanners.ForestComponents

namespace LightEFTSpanners.StoredVertexPairs

def typedPairs {n : ℕ} (xs ys : List (Fin n)) : List (Fin n × Fin n) :=
  xs.flatMap fun x => ys.map fun y => (x,y)

theorem pairs_encoded {n : ℕ} (xs ys : List (Fin n)) :
    pairs (xs.map Fin.val) (ys.map Fin.val)=StoredEdges.encode (typedPairs xs ys) := by
  simp [pairs,typedPairs,StoredEdges.encode,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]

theorem mem_square {n : ℕ} (xs : List (Fin n)) (u v : Fin n) :
    s(u,v)∈StoredSample.edgeSet (typedPairs xs xs) ↔ u∈xs ∧ v∈xs := by
  simp only [StoredSample.edgeSet,List.mem_toFinset,List.mem_map,typedPairs,List.mem_flatMap]
  constructor
  · rintro ⟨⟨a,b⟩,⟨x,hx,y,hy,hxy⟩,he⟩
    cases hxy
    rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hx,hy⟩
    · exact ⟨hy,hx⟩
  · rintro ⟨hu,hv⟩
    exact ⟨(u,v),⟨u,hu,v,hv,rfl⟩,rfl⟩

/-- A supplied component vertex enumeration now generates its entire eligible
endpoint relation, including diagonal pairs, rather than supplying that relation. -/
theorem component_incidence {n : ℕ} (F : SimpleGraph (Fin n)) (c : F.ConnectedComponent)
    (xs : List (Fin n)) (vertices : ∀ v,v∈xs ↔ v∈c.supp) (u v : Fin n) :
    s(u,v)∈StoredSample.edgeSet (typedPairs xs xs) ↔
      ∃ e,(componentEmbedding F c).sym2Map e=s(u,v) := by
  rw [mem_square,vertices u,vertices v,component_pair_preimage]

def execute (xs ys : List ℕ) : List StoredEdges.Edge :=
  match Controller.run transition (steps xs ys) (.rows xs ys []) with
  | .halt out => out
  | _ => []

@[simp] theorem execute_eq (xs ys : List ℕ) : execute xs ys=pairs xs ys := by
  simp only [execute,(pairs_trace xs ys).run_eq]

theorem execute_encoded {n : ℕ} (xs ys : List (Fin n)) :
    execute (xs.map Fin.val) (ys.map Fin.val)=StoredEdges.encode (typedPairs xs ys) := by
  rw [execute_eq,pairs_encoded]
end LightEFTSpanners.StoredVertexPairs
