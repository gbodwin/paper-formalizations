import MinorFreeSpanners.BranchingConnectorBudget

/-! Original connector identities remain disjoint when different output
carriers use different chosen coarse subgraphs. All identities use the same
old-host crossing embedding, enabling pooled credit without duplicate edges. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I]
variable {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem connectorEdges_disjoint_graphs (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (hT : T≤G) (H K : SimpleGraph I)
    (hH : H≤C.graph T) (hK : K≤C.graph T)
    (S U : Finset I) (hSU : Disjoint S U) :
    Disjoint (C.connectorEdges hA hT H hH S) (C.connectorEdges hA hT K hK U) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e hs hu
  unfold connectorEdges at hs hu
  obtain ⟨f,_,hf⟩ := Finset.mem_image.mp hs
  obtain ⟨g,_,hg⟩ := Finset.mem_image.mp hu
  have hh := (C.crossingEmbedding hA hT).injective (Subtype.ext (hf.trans hg.symm))
  have heq := congrArg (fun q : (C.graph T).edgeSet => q.val) hh
  obtain ⟨hfe,hfS⟩ := Finset.mem_filter.mp f.property
  obtain ⟨hge,hgU⟩ := Finset.mem_filter.mp g.property
  obtain ⟨x,hx⟩ : f.val.toFinset.Nonempty := by
    induction f.val using Sym2.inductionOn with
    | _ x y => exact ⟨x,by simp⟩
  have hxS : x∈S := hfS hx
  have hxU : x∈U := hgU (heq ▸ hx)
  exact Finset.disjoint_left.mp hSU hxS hxU

 theorem connectorEdges_variable_weight_total_le [Fintype V] {J : Type*} [Fintype J]
    (C : ClusterFamily (I := I) A w D) (hA : A≤G) (hT : T≤G)
    (H : J → SimpleGraph I) (hH : ∀ j,H j≤C.graph T)
    (S : J → Finset I) (hS : ∀ i j,i≠j → Disjoint (S i) (S j))
    (hw : ∀ e∈T.edgeSet,0≤w e) :
    (∑ j,∑ e∈C.connectorEdges hA hT (H j) (hH j) (S j),w e)≤∑ e∈T.edgeFinset,w e := by
  classical
  have hd : (↑(Finset.univ : Finset J) : Set J).PairwiseDisjoint
      (fun j => C.connectorEdges hA hT (H j) (hH j) (S j)) := by
    intro i _ j _ hij
    exact C.connectorEdges_disjoint_graphs hA hT (H i) (H j) (hH i) (hH j) (S i) (S j) (hS i j hij)
  rw [←Finset.sum_biUnion hd]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨j,_,he⟩ := Finset.mem_biUnion.mp he
    exact mem_edgeFinset.mpr (C.connectorEdges_mem hA hT (H j) (hH j) (S j) he)
  · intro e he _
    exact hw e (mem_edgeFinset.mp he)

end ClusterFamily
end MinorFreeSpanners
