import MinorFreeSpanners.ClusterMergeWalk

/-! Retain each selected large cluster as one root and each unused old cluster
as one residual vertex. No old cluster is split or duplicated. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

abbrev SelectedResidualIndex {I : Type*} (P : Finset (Finset I)) :=
  Sum {S // S∈P} {i // i∉P.biUnion id}

namespace ClusterFamily
variable {I V : Type*} {A G : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}

noncomputable def selectedResidual (C : ClusterFamily (I:=I) A w D) (hA : A≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i}) :
    ClusterFamily (I:=SelectedResidualIndex P) G w (max D E) where
  branch := Sum.elim F.branch (fun i => C.branch i.val)
  nonempty := by intro j;cases j with | inl S => exact F.nonempty S | inr i => exact C.nonempty i.val
  disjoint := by
    intro j k hjk
    cases j with
    | inl S =>
      cases k with
      | inl T => exact F.disjoint S T (fun he => hjk (congrArg Sum.inl he))
      | inr i =>
        apply Set.disjoint_left.mpr
        intro x hx hi
        change x∈F.branch S at hx
        rw [hbranch S] at hx
        obtain ⟨j,hj,hx⟩ := hx
        have hji : j≠i.val := by
          intro he;exact i.property (Finset.mem_biUnion.mpr ⟨S.val,S.property,he ▸ hj⟩)
        exact Set.disjoint_left.mp (C.disjoint j i.val hji) hx hi
    | inr i =>
      cases k with
      | inl S =>
        apply Set.disjoint_left.mpr
        intro x hi hx
        change x∈F.branch S at hx
        rw [hbranch S] at hx
        obtain ⟨j,hj,hx⟩ := hx
        have hji : j≠i.val := by
          intro he;exact i.property (Finset.mem_biUnion.mpr ⟨S.val,S.property,he ▸ hj⟩)
        exact Set.disjoint_left.mp (C.disjoint j i.val hji) hx hi
      | inr j => exact C.disjoint i.val j.val (fun he => hjk (congrArg Sum.inr (Subtype.ext he)))
  connected := by
    intro j x hx y hy
    cases j with
    | inl S =>
      obtain ⟨p,hp,hw⟩ := F.connected S x hx y hy
      exact ⟨p,hp,hw.trans (le_max_right _ _)⟩
    | inr i =>
      obtain ⟨p,hp,hw⟩ := C.connected i.val x hx y hy
      exact ⟨p.mapLe hA,by simpa using hp,by simpa using hw.trans (le_max_left D E)⟩

 theorem selectedResidual_covers (C : ClusterFamily (I:=I) A w D) (hA : A≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (hcover : ∀ x,∃ i,x∈C.branch i) :
    ∀ x,∃ j,x∈(C.selectedResidual hA P F hbranch).branch j := by
  classical
  intro x
  obtain ⟨i,hi⟩ := hcover x
  by_cases hU : i∈P.biUnion id
  · obtain ⟨S,hS,hiS⟩ := Finset.mem_biUnion.mp hU
    refine ⟨Sum.inl ⟨S,hS⟩,?_⟩
    change x∈F.branch ⟨S,hS⟩
    rw [hbranch]
    exact ⟨i,hiS,hi⟩
  · exact ⟨Sum.inr ⟨i,hU⟩,hi⟩

 theorem selectedResidual_intrinsic (C : ClusterFamily (I:=I) A w D) (hA : A≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (d : I → ℝ) (radius : {S // S∈P} → ℝ)
    (hC : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : A.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (hF : ∀ S x,x∈F.branch S → ∀ y,y∈F.branch S →
      ∃ p : G.Walk x y,(∀ z∈p.support,z∈F.branch S) ∧ walkWeight w p≤radius S) :
    let B := C.selectedResidual hA P F hbranch
    ∀ j x,x∈B.branch j → ∀ y,y∈B.branch j →
      ∃ p : G.Walk x y,(∀ z∈p.support,z∈B.branch j) ∧
        walkWeight w p≤Sum.elim radius (fun i => d i.val) j := by
  intro B j x hx y hy
  cases j with
  | inl S => exact hF S x hx y hy
  | inr i =>
    obtain ⟨p,hp,hw⟩ := hC i.val x hx y hy
    exact ⟨p.mapLe hA,by simpa [B,selectedResidual] using hp,by simpa using hw⟩

end ClusterFamily
end MinorFreeSpanners
