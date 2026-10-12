import MinorFreeSpanners.MarkedClusterEdges
import MinorFreeSpanners.ExactConnectorPooling

/-! A singleton artificial high root has no earlier internal heavy-edge bill
and no old forest connector. Edges to residual clusters remain for the later
heavy-edge construction; they are not charged by this initialization lemma. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem ClusterFamily.markedEdges_singleton_empty {I V : Type*} [Fintype V]
    {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I:=I) A w D)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬B.Adj x y) (i : I) :
    C.markedEdges B {i}=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,j,hj,k,hk,x,hx,y,hy,rfl⟩ := Finset.mem_filter.mp he
  have hji : j=i := Finset.mem_singleton.mp hj
  have hki : k=i := Finset.mem_singleton.mp hk
  subst j;subst k
  exact hloop i x hx y hy (mem_edgeFinset.mp he)

 theorem internalEdges_singleton_empty {I : Type*} [Fintype I] (H : SimpleGraph I) (i : I) :
    internalEdges H {i}=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨he,hs⟩ := Finset.mem_filter.mp he
    have hxi : x=i := Finset.mem_singleton.mp (hs (by simp))
    have hyi : y=i := Finset.mem_singleton.mp (hs (by simp))
    subst x;subst y
    exact H.loopless.irrefl i (mem_edgeFinset.mp he)

 theorem ClusterFamily.connectorEdges_singleton_empty {I V : Type*} [Fintype I]
    {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hT : T≤G)
    (H : SimpleGraph I) (hH : H≤C.graph T) (i : I) :
    C.connectorEdges hA hT H hH {i}=∅ := by
  classical
  apply Finset.card_eq_zero.mp
  rw [C.connectorEdges_card,internalEdges_singleton_empty]
  rfl

end MinorFreeSpanners
