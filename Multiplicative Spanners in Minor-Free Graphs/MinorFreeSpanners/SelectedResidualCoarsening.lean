import MinorFreeSpanners.SelectedResidualClusters
import MinorFreeSpanners.CoarsenedConnectorFreshness

/-! The actual mixed selected/residual family coarsens every original branch.
Consequently every connector chosen across it is external to all old branches,
including when the selected family is empty. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem ClusterFamily.selectedResidual_coarsens {I V : Type*}
    {A G : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i}) :
    ∀ i,∃ j,C.branch i⊆(C.selectedResidual hA P F hbranch).branch j := by
  classical
  intro i
  by_cases hi : i∈P.biUnion id
  · obtain ⟨S,hS,hiS⟩ := Finset.mem_biUnion.mp hi
    refine ⟨Sum.inl ⟨S,hS⟩,?_⟩
    intro x hx
    change x∈F.branch ⟨S,hS⟩
    rw [hbranch]
    exact ⟨i,hiS,hx⟩
  · exact ⟨Sum.inr ⟨i,hi⟩,fun _ hx => hx⟩

 theorem ClusterFamily.selectedResidual_connectorPool_external {I J V : Type*}
    [Fintype I] [Fintype J]
    {A G T : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hT : T≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (H : J → SimpleGraph (SelectedResidualIndex P))
    (hH : ∀ j,H j≤(C.selectedResidual hA P F hbranch).graph T)
    (S : J → Finset (SelectedResidualIndex P))
    {e : Sym2 V} (he : e∈(C.selectedResidual hA P F hbranch).connectorPool le_rfl hT H hH S)
    (i : I) (x y : V) (hx : x∈C.branch i) (hy : y∈C.branch i) : e≠s(x,y) := by
  exact coarsened_connectorPool_fresh C (C.selectedResidual hA P F hbranch)
    (C.selectedResidual_coarsens hA P F hbranch) hT H hH S he i x y hx hy

end MinorFreeSpanners
