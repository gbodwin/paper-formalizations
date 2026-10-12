import MinorFreeSpanners.SelectedRootPriorLabels

/-! Reindex actual selected clusters by their literal old-label groups.
Disjoint nonempty host branches prove that no two original roots give the
same group. The original branch carriers and walks are retained unchanged. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I J K V : Type*} {A G : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}

def reindex (F : ClusterFamily (I:=J) G w E) (e : K ≃ J) :
    ClusterFamily (I:=K) G w E where
  branch := fun k => F.branch (e k)
  nonempty := fun k => F.nonempty (e k)
  disjoint := fun j k h => F.disjoint (e j) (e k) (fun he => h (e.injective he))
  connected := fun k => F.connected (e k)

 theorem original_groups_injective (C : ClusterFamily (I:=I) A w D)
    (F : ClusterFamily (I:=J) G w E) (groups : J → Finset I)
    (hbranch : ∀ j,F.branch j={x | ∃ i∈groups j,x∈C.branch i}) : Function.Injective groups := by
  intro j k he
  by_contra hne
  obtain ⟨x,hx⟩ := F.nonempty j
  have hk : x∈F.branch k := by
    rw [hbranch k,←he,←hbranch j]
    exact hx
  exact Set.disjoint_left.mp (F.disjoint j k hne) hx hk

 theorem original_groups_disjoint (C : ClusterFamily (I:=I) A w D)
    (F : ClusterFamily (I:=J) G w E) (groups : J → Finset I)
    (hbranch : ∀ j,F.branch j={x | ∃ i∈groups j,x∈C.branch i}) :
    ∀ j k,j≠k → Disjoint (groups j) (groups k) := by
  intro j k hne
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨x,hx⟩ := C.nonempty i
  exact Set.disjoint_left.mp (F.disjoint j k hne)
    (by rw [hbranch];exact ⟨i,hi,hx⟩) (by rw [hbranch];exact ⟨i,hj,hx⟩)

noncomputable def originalGroupEquiv [Fintype J] (C : ClusterFamily (I:=I) A w D)
    (F : ClusterFamily (I:=J) G w E) (groups : J → Finset I)
    (hbranch : ∀ j,F.branch j={x | ∃ i∈groups j,x∈C.branch i}) :
    J ≃ {S // S∈(Finset.univ.image groups)} :=
  Equiv.ofBijective (fun j => ⟨groups j,Finset.mem_image.mpr ⟨j,mem_univ j,rfl⟩⟩) ⟨by
    intro j k he
    exact C.original_groups_injective F groups hbranch (congrArg Subtype.val he),by
    rintro ⟨S,hS⟩
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hS
    exact ⟨j,rfl⟩⟩

 theorem reindexed_group_branch [Fintype J] (C : ClusterFamily (I:=I) A w D)
    (F : ClusterFamily (I:=J) G w E) (groups : J → Finset I)
    (hbranch : ∀ j,F.branch j={x | ∃ i∈groups j,x∈C.branch i})
    (S : {S // S∈(Finset.univ.image groups)}) :
    (F.reindex (C.originalGroupEquiv F groups hbranch).symm).branch S=
      {x | ∃ i∈S.val,x∈C.branch i} := by
  change F.branch ((C.originalGroupEquiv F groups hbranch).symm S)=_
  rw [hbranch]
  have he := congrArg Subtype.val ((C.originalGroupEquiv F groups hbranch).apply_symm_apply S)
  change groups ((C.originalGroupEquiv F groups hbranch).symm S)=S.val at he
  rw [he]

end ClusterFamily
end MinorFreeSpanners
