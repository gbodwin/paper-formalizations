import LightEFTSpanners.SubdivisionForcing
import LightSpanners.CopyWeights

namespace LightEFTSpanners.ParallelSubdivision
open SimpleGraph Finset LightSpanners
variable {V I : Type*} [Fintype V] [Fintype I] (C D : SimpleGraph V)
attribute [local instance] Classical.propDecidable

omit [Fintype V] [Fintype I] in
theorem coreGraph_eq_map :
    coreGraph (I:=I) C D=D.map (Function.Embedding.inl : V ↪ Vertex (I:=I) C) := by
  ext a b
  rw [SimpleGraph.map_adj]
  cases a <;> cases b <;> simp [coreGraph]

theorem core_edgeFinset : (coreGraph (I:=I) C D).edgeFinset=
    D.edgeFinset.map (Function.Embedding.inl : V ↪ Vertex (I:=I) C).sym2Map := by
  apply Finset.coe_injective
  simp only [coe_edgeFinset,coe_map]
  rw [coreGraph_eq_map,edgeSet_map]

theorem core_edge_count : (coreGraph (I:=I) C D).edgeFinset.card=D.edgeFinset.card := by
  rw [core_edgeFinset,card_map]

theorem core_totalWeight (W : ℝ) :
    totalWeight (coreGraph (I:=I) C C) (coreWeight C W)=C.edgeFinset.card*W := by
  rw [totalWeight_eq_card_mul _ _ W (by intro e he; simp [coreWeight,he]),core_edge_count]

omit [Fintype V] [Fintype I] in
theorem coreWeight_unit (W : ℝ) {e : Sym2 (Vertex (I:=I) C)}
    (he : e∈(graph C).edgeSet) : coreWeight C W e=1 := by
  have hnot : e∉(coreGraph C C).edgeSet := by
    rcases e with ⟨a,b⟩
    simp only [mem_edgeSet] at he ⊢
    cases a <;> cases b <;> simp_all [graph,coreGraph]
  simp [coreWeight,hnot]

omit [Fintype V] [Fintype I] in
theorem coreWeight_positive {W : ℝ} (hW : 0<W) (e : Sym2 (Vertex (I:=I) C)) :
    0<coreWeight C W e := by
  unfold coreWeight
  split_ifs <;> positivity

theorem core_retention_weight {W : ℝ} (hW : 0≤W)
    {H : SimpleGraph (Vertex (I:=I) C)} (hH : coreGraph C C≤H) :
    C.edgeFinset.card*W≤totalWeight H (coreWeight C W) := by
  rw [← core_totalWeight (I:=I) C W]
  apply totalWeight_mono_subgraph hH
  intro e _
  unfold coreWeight
  split_ifs <;> positivity
end LightEFTSpanners.ParallelSubdivision
