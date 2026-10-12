import MinorFreeSpanners.VariableConnectorDisjoint
import MinorFreeSpanners.FourArmCoreBudget

/-! Original connector budgets extend monotonically to larger coarse carriers.
This permits a previously paid root and newly absorbed disjoint path blocks to
share one actual original-edge ledger without reusing either resource. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I]
variable {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem connectorEdges_mono_graph_carrier (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (H K : SimpleGraph I)
    (hH : H≤C.graph T) (hK : K≤C.graph T) (hHK : H≤K)
    {S U : Finset I} (hSU : S⊆U) :
    C.connectorEdges hA hT H hH S⊆C.connectorEdges hA hT K hK U := by
  classical
  intro e he
  unfold connectorEdges at he ⊢
  obtain ⟨f,_,hf⟩ := Finset.mem_image.mp he
  have hm : f.val∈internalEdges K U := by
    obtain ⟨he,hs⟩ := Finset.mem_filter.mp f.property
    exact Finset.mem_filter.mpr ⟨edgeFinset_mono hHK he,hs.trans hSU⟩
  refine Finset.mem_image.mpr ⟨⟨f.val,hm⟩,Finset.mem_attach _ _,?_⟩
  exact hf

 theorem root_block_connector_budget (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (H K : SimpleGraph I)
    (hH : H≤C.graph T) (hK : K≤C.graph T)
    (root : Finset I) (P : Finset (Finset I))
    (hdis : Disjoint root (P.biUnion id)) (hw : ∀ e∈T.edgeSet,0≤w e) :
    (∑ e∈C.connectorEdges hA hT K hK root,w e)+
      (∑ e∈P.biUnion (fun S => C.connectorEdges hA hT H hH S),w e)≤
      ∑ e∈C.connectorEdges hA hT (C.graph T) le_rfl (root∪P.biUnion id),w e := by
  classical
  have hd : Disjoint (C.connectorEdges hA hT K hK root)
      (P.biUnion (fun S => C.connectorEdges hA hT H hH S)) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨S,hS,hf⟩ := Finset.mem_biUnion.mp hf
    have hs : S⊆P.biUnion id := fun i hi => Finset.mem_biUnion.mpr ⟨S,hS,hi⟩
    exact Finset.disjoint_left.mp
      (C.connectorEdges_disjoint_graphs hA hT K H hK hH root S (hdis.mono_right hs)) he hf
  rw [←Finset.sum_union hd]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact C.connectorEdges_mono_graph_carrier hA hT K (C.graph T) hK le_rfl hK
        Finset.subset_union_left he
    · obtain ⟨S,hS,he⟩ := Finset.mem_biUnion.mp he
      apply C.connectorEdges_mono_graph_carrier hA hT H (C.graph T) hH le_rfl hH _ he
      exact fun i hi => Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨S,hS,hi⟩)
  · intro e he _
    exact hw e (C.connectorEdges_mem hA hT (C.graph T) le_rfl _ he)

 theorem root_block_credit_provenance (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (H K : SimpleGraph I)
    (hH : H≤C.graph T) (hK : K≤C.graph T)
    (root : Finset I) (P : Finset (Finset I)) (credit : I → ℝ)
    (c R spare spent cost : ℝ) (hc : 0≤c)
    (hdis : Disjoint root (P.biUnion id)) (hw : ∀ e∈T.edgeSet,0≤w e)
    (hroot : spent+c*R+spare≤(∑ i∈root,credit i)+
      c*(∑ e∈C.connectorEdges hA hT K hK root,w e))
    (hnew : cost≤c*R+spare+(∑ i∈P.biUnion id,credit i)+
      c*(∑ e∈P.biUnion (fun S => C.connectorEdges hA hT H hH S),w e)) :
    spent+cost≤(∑ i∈root∪P.biUnion id,credit i)+
      c*(∑ e∈C.connectorEdges hA hT (C.graph T) le_rfl (root∪P.biUnion id),w e) := by
  rw [Finset.sum_union hdis]
  have he := mul_le_mul_of_nonneg_left
    (C.root_block_connector_budget hA hT H K hH hK root P hdis hw) hc
  nlinarith

end ClusterFamily
end MinorFreeSpanners
