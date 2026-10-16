import LightEFTSpanners.StoredForestOutputLaw

namespace LightEFTSpanners.StoredForestCandidates
attribute [local instance] Classical.propDecidable

noncomputable def graphEdges {n : ℕ} (G : SimpleGraph (Fin n)) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u =>
    ((List.finRange n).filter fun v => decide (G.Adj u v)).map (Prod.mk u)

theorem mem_graphEdges {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    (u,v)∈graphEdges G ↔ G.Adj u v := by
  simp [graphEdges]

theorem graphEdges_mem_set {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    s(u,v)∈StoredSample.edgeSet (graphEdges G) ↔ G.Adj u v := by
  simp only [StoredSample.edgeSet,List.mem_toFinset,List.mem_map]
  constructor
  · rintro ⟨⟨a,b⟩,hab,he⟩
    have hadj := (mem_graphEdges G a b).mp hab
    rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hadj
    · exact hadj.symm
  · intro h
    exact ⟨(u,v),(mem_graphEdges G u v).mpr h,rfl⟩

theorem graphEdges_graph {n : ℕ} (G : SimpleGraph (Fin n)) :
    ExecutableVoting.graph (StoredSample.edgeSet (graphEdges G))=G := by
  ext u v
  change s(u,v)∈StoredSample.edgeSet (graphEdges G) ∧ u≠v ↔ G.Adj u v
  rw [graphEdges_mem_set]
  exact ⟨And.left,fun h => ⟨h,G.ne_of_adj h⟩⟩

theorem represented_family {n q : ℕ} (F : Fin q → SimpleGraph (Fin n)) :
    StoredForestHosts.family (fun i => graphEdges (F i))=F := by
  funext i
  exact graphEdges_graph (F i)
end LightEFTSpanners.StoredForestCandidates
