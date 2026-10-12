import MinorFreeSpanners.SingletonAnchorTree

/-! The singleton-root tree lives in the exact mixed cluster graph, not just
an isomorphic abstract tree. This preserves the original MST-edge carrier for
subsequent short and heavy absorption. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem singletonAnchorTree_subgraph {I V : Type*} {A G T : SimpleGraph V}
    {w : Sym2 V → ℝ} {D E : ℝ} (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (anchor : I) (hDE : D≤E)
    (H : SimpleGraph I) (hH : H≤C.graph T) :
    singletonAnchorTree H anchor≤
      (C.selectedResidual hA {{anchor}} (singletonAnchorFamily C hA anchor hDE)
        (singletonAnchorFamily_branch C hA anchor hDE)).graph T := by
  let F := singletonAnchorFamily C hA anchor hDE
  let C0 := C.selectedResidual hA {{anchor}} F (singletonAnchorFamily_branch C hA anchor hDE)
  have hb : ∀ j,C0.branch j=C.branch (singletonAnchorEquiv anchor j) := by
    intro j
    cases j <;> rfl
  intro j k hjk
  change H.Adj (singletonAnchorEquiv anchor j) (singletonAnchorEquiv anchor k) at hjk
  obtain ⟨hne,x,hx,y,hy,hxy⟩ := hH hjk
  refine ⟨fun he => hne (congrArg (singletonAnchorEquiv anchor) he),x,?_,y,?_,hxy⟩
  · change x∈C0.branch j
    rwa [hb]
  · change y∈C0.branch k
    rwa [hb]

end MinorFreeSpanners
