import MinorFreeSpanners.ClusterConnectorEdges

/-! Each internal edge of a selected coarse forest receives a different actual
unit host edge. Disjoint cores therefore use disjoint original connector credit. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
namespace ClusterFamily
variable {I V : Type*} [Fintype I] {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
attribute [local instance] Classical.propDecidable

noncomputable def connectorEdges (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (hT : T≤G) (H : SimpleGraph I) (hH : H≤C.graph T)
    (S : Finset I) : Finset (Sym2 V) := by
  classical
  exact (internalEdges H S).attach.image fun e =>
    (C.crossingEmbedding hA hT ⟨e.val,
      SimpleGraph.edgeSet_mono hH (mem_edgeFinset.mp (Finset.mem_filter.mp e.property).1)⟩).val

lemma connectorEdges_card (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (hT : T≤G) (H : SimpleGraph I) (hH : H≤C.graph T) (S : Finset I) :
    (C.connectorEdges hA hT H hH S).card=(internalEdges H S).card := by
  classical
  unfold connectorEdges
  rw [Finset.card_image_of_injective,Finset.card_attach]
  intro e f he
  apply Subtype.ext
  have hh := (C.crossingEmbedding hA hT).injective (Subtype.ext he)
  exact congrArg (fun q : (C.graph T).edgeSet => q.val) hh

lemma connectorEdges_mem (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (hT : T≤G) (H : SimpleGraph I) (hH : H≤C.graph T)
    (S : Finset I) {e : Sym2 V} (he : e∈C.connectorEdges hA hT H hH S) : e∈T.edgeSet := by
  classical
  unfold connectorEdges at he
  obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp he
  exact (C.crossingEmbedding hA hT _).property

lemma connectorEdges_disjoint (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (hT : T≤G) (H : SimpleGraph I) (hH : H≤C.graph T)
    (S U : Finset I) (hSU : Disjoint S U) :
    Disjoint (C.connectorEdges hA hT H hH S) (C.connectorEdges hA hT H hH U) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e hs hu
  unfold connectorEdges at hs hu
  obtain ⟨f,_,hf⟩ := Finset.mem_image.mp hs
  obtain ⟨g,_,hg⟩ := Finset.mem_image.mp hu
  have hh := (C.crossingEmbedding hA hT).injective (Subtype.ext (hf.trans hg.symm))
  have heq := congrArg (fun q : (C.graph T).edgeSet => q.val) hh
  exact Finset.disjoint_left.mp (internalEdges_disjoint H hSU) f.property (heq ▸ g.property)

lemma connectorEdges_fresh (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (hT : T≤G) (H : SimpleGraph I) (hH : H≤C.graph T)
    (S : Finset I) {e : Sym2 V} (he : e∈C.connectorEdges hA hT H hH S)
    (i : I) (x y : V) (hx : x∈C.branch i) (hy : y∈C.branch i) : e≠s(x,y) := by
  classical
  unfold connectorEdges at he
  obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp he
  exact C.crossingEmbedding_not_internal hA hT _ i x y hx hy

lemma connectorEdges_unit_weight (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (hT : T≤G) (H : SimpleGraph I) (hH : H≤C.graph T)
    (S : Finset I) (hunit : ∀ e∈T.edgeSet,w e=1) :
    (∑ e∈C.connectorEdges hA hT H hH S,w e)=(internalEdges H S).card := by
  classical
  calc
    _ = ∑ _e∈C.connectorEdges hA hT H hH S,(1:ℝ) :=
      Finset.sum_congr rfl fun e he => hunit e (C.connectorEdges_mem hA hT H hH S he)
    _ = _ := by simp [C.connectorEdges_card hA hT H hH S]

lemma connectorEdges_total_le [Fintype V] {J : Type*} [Fintype J]
    (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (hT : T≤G) (H : SimpleGraph I) (hH : H≤C.graph T)
    (S : J → Finset I) (hS : ∀ i j,i≠j → Disjoint (S i) (S j)) :
    ∑ i,(C.connectorEdges hA hT H hH (S i)).card≤T.edgeFinset.card := by
  classical
  have hd : (↑(Finset.univ : Finset J) : Set J).PairwiseDisjoint
      (fun i => C.connectorEdges hA hT H hH (S i)) := by
    intro i hi j hj hij
    exact C.connectorEdges_disjoint hA hT H hH (S i) (S j) (hS i j hij)
  rw [← Finset.card_biUnion hd]
  apply Finset.card_le_card
  intro e he
  obtain ⟨i,_,he⟩ := Finset.mem_biUnion.mp he
  exact mem_edgeFinset.mpr (C.connectorEdges_mem hA hT H hH (S i) he)

end ClusterFamily
end MinorFreeSpanners
