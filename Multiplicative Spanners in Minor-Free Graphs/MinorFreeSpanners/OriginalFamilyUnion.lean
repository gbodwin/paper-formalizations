import MinorFreeSpanners.ActualGroupReindex

/-! Combine actual root families on disjoint original label groups, keeping
literal host carriers and the already supplied internal walks. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} {A G : SimpleGraph V} {w : Sym2 V → ℝ} {D U W : ℝ}

noncomputable def unionOriginal (C : ClusterFamily (I:=I) A w D)
    (P Q : Finset (Finset I))
    (F : ClusterFamily (I:={S // S∈P}) G w U)
    (K : ClusterFamily (I:={S // S∈Q}) G w W)
    (hF : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (hK : ∀ S,K.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (cross : ∀ S∈P,∀ Z∈Q,Disjoint S Z) :
    ClusterFamily (I:={S // S∈P∪Q}) G w (max U W) := by
  classical
  have nonempty (S : {S // S∈P∪Q}) : ({x | ∃ i∈S.val,x∈C.branch i} : Set V).Nonempty := by
    rcases Finset.mem_union.mp S.property with hS|hS
    · simpa only [hF] using F.nonempty ⟨S.val,hS⟩
    · simpa only [hK] using K.nonempty ⟨S.val,hS⟩
  have disj : ∀ S Z,S∈P∪Q → Z∈P∪Q → S≠Z → Disjoint S Z := by
    intro S Z hS hZ hne
    rcases Finset.mem_union.mp hS with hS|hS <;> rcases Finset.mem_union.mp hZ with hZ|hZ
    · exact C.original_groups_disjoint F Subtype.val hF ⟨S,hS⟩ ⟨Z,hZ⟩
        (fun he => hne (congrArg Subtype.val he))
    · exact cross S hS Z hZ
    · exact (cross Z hZ S hS).symm
    · exact C.original_groups_disjoint K Subtype.val hK ⟨S,hS⟩ ⟨Z,hZ⟩
        (fun he => hne (congrArg Subtype.val he))
  exact {
    branch := fun S => {x | ∃ i∈S.val,x∈C.branch i}
    nonempty := nonempty
    disjoint := by
      intro S Z hne
      apply Set.disjoint_left.mpr
      rintro x ⟨i,hi,hxi⟩ ⟨j,hj,hxj⟩
      have he : i=j := by
        by_contra hij
        exact Set.disjoint_left.mp (C.disjoint i j hij) hxi hxj
      subst j
      exact Finset.disjoint_left.mp (disj S.val Z.val S.property Z.property
        (fun he => hne (Subtype.ext he))) hi hj
    connected := by
      intro S x hx y hy
      rcases Finset.mem_union.mp S.property with hS|hS
      · obtain ⟨p,hp,hw⟩ := F.connected ⟨S.val,hS⟩ x (by simpa only [hF] using hx)
          y (by simpa only [hF] using hy)
        exact ⟨p,by simpa only [hF] using hp,hw.trans (le_max_left _ _)⟩
      · obtain ⟨p,hp,hw⟩ := K.connected ⟨S.val,hS⟩ x (by simpa only [hK] using hx)
          y (by simpa only [hK] using hy)
        exact ⟨p,by simpa only [hK] using hp,hw.trans (le_max_right _ _)⟩ }

 theorem unionOriginal_branch (C : ClusterFamily (I:=I) A w D)
    (P Q : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w U)
    (K : ClusterFamily (I:={S // S∈Q}) G w W)
    (hF : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (hK : ∀ S,K.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (cross : ∀ S∈P,∀ Z∈Q,Disjoint S Z) (S : {S // S∈P∪Q}) :
    (C.unionOriginal P Q F K hF hK cross).branch S={x | ∃ i∈S.val,x∈C.branch i} := rfl

end ClusterFamily
end MinorFreeSpanners
