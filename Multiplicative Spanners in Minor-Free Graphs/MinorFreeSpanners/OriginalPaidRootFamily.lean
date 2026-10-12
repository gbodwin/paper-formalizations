import MinorFreeSpanners.ActualGroupReindex
import MinorFreeSpanners.WeightedShortCyclePhase

/-! A carrier-preserving record for actual weak-root outputs. Merging uses
literal old-label unions and keeps each root's radius, intrinsic walks and
original touching-edge/connector bill. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

structure OriginalPaidRootFamily {I V : Type*} [Fintype I] [Fintype V]
    {A B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hT : T≤G)
    (H : SimpleGraph I) (hH : H≤C.graph T) (credit : I → ℝ) (c reserve U : ℝ) where
  groups : Finset (Finset I)
  family : ClusterFamily (I:={S // S∈groups}) G w U
  branch : ∀ S,family.branch S={x | ∃ i∈S.val,x∈C.branch i}
  radius : {S // S∈groups} → ℝ
  radius_nonneg : ∀ S,0≤radius S
  radius_le : ∀ S,radius S≤U
  intrinsic : ∀ S x,x∈family.branch S → ∀ y,y∈family.branch S →
    ∃ p : G.Walk x y,(∀ z∈p.support,z∈family.branch S) ∧ walkWeight w p≤radius S
  paid : ∀ S,(∑ e∈C.touchingEdges B S.val,w e)+c*radius S+reserve≤
    (∑ i∈S.val,credit i)+c*(∑ e∈C.connectorEdges hA hT H hH S.val,w e)

namespace OriginalPaidRootFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
variable {C : ClusterFamily (I:=I) A w D} {hA : A≤G} {hT : T≤G}
variable {H : SimpleGraph I} {hH : H≤C.graph T} {credit : I → ℝ} {c reserve U : ℝ}

noncomputable def ofPhase {U₀ : ℝ} (P : Finset (Finset I))
    (F : ClusterFamily (I:={S // S∈P}) G w U₀)
    (branch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (radius : {S // S∈P} → ℝ) (rad0 : ∀ S,0≤radius S) (radU : ∀ S,radius S≤U)
    (intrinsic : ∀ S x,x∈F.branch S → ∀ y,y∈F.branch S →
      ∃ p : G.Walk x y,(∀ z∈p.support,z∈F.branch S) ∧ walkWeight w p≤radius S)
    (paid : ∀ S,(∑ e∈C.touchingEdges B S.val,w e)+c*radius S+reserve≤
      (∑ i∈S.val,credit i)+c*(∑ e∈C.connectorEdges hA hT H hH S.val,w e)) :
    OriginalPaidRootFamily (B:=B) C hA hT H hH credit c reserve U where
  groups := P
  family := {
    branch := F.branch
    nonempty := F.nonempty
    disjoint := F.disjoint
    connected := by
      intro S x hx y hy
      obtain ⟨p,hp,hw⟩ := intrinsic S x hx y hy
      exact ⟨p,hp,hw.trans (radU S)⟩}
  branch := branch
  radius := radius
  radius_nonneg := rad0
  radius_le := radU
  intrinsic := intrinsic
  paid := paid

 theorem disjoint (F : OriginalPaidRootFamily (B:=B) C hA hT H hH credit c reserve U) :
    ∀ S Z,S∈F.groups → Z∈F.groups → S≠Z → Disjoint S Z := by
  intro S Z hS hZ hne
  exact C.original_groups_disjoint F.family Subtype.val F.branch ⟨S,hS⟩ ⟨Z,hZ⟩
    (fun he => hne (congrArg Subtype.val he))

noncomputable def merge
    (X Y : OriginalPaidRootFamily (B:=B) C hA hT H hH credit c reserve U)
    (cross : ∀ S∈X.groups,∀ Z∈Y.groups,Disjoint S Z) :
    OriginalPaidRootFamily (B:=B) C hA hT H hH credit c reserve U := by
  classical
  let P := X.groups∪Y.groups
  have memY (S : {S // S∈P}) (h : S.val∉X.groups) : S.val∈Y.groups :=
    (Finset.mem_union.mp S.property).resolve_left h
  let radius : {S // S∈P} → ℝ := fun S =>
    if h : S.val∈X.groups then X.radius ⟨S.val,h⟩ else Y.radius ⟨S.val,memY S h⟩
  have hdis : ∀ S Z,S∈P → Z∈P → S≠Z → Disjoint S Z := by
    intro S Z hS hZ hne
    rcases Finset.mem_union.mp hS with hS|hS <;> rcases Finset.mem_union.mp hZ with hZ|hZ
    · exact X.disjoint S Z hS hZ hne
    · exact cross S hS Z hZ
    · exact (cross Z hZ S hS).symm
    · exact Y.disjoint S Z hS hZ hne
  have nonempty (S : {S // S∈P}) : ({x | ∃ i∈S.val,x∈C.branch i} : Set V).Nonempty := by
    by_cases h : S.val∈X.groups
    · simpa only [X.branch] using X.family.nonempty ⟨S.val,h⟩
    · simpa only [Y.branch] using Y.family.nonempty ⟨S.val,memY S h⟩
  have walks (S : {S // S∈P}) (x : V) (hx : ∃ i∈S.val,x∈C.branch i)
      (y : V) (hy : ∃ i∈S.val,y∈C.branch i) :
      ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈S.val,z∈C.branch i) ∧ walkWeight w p≤radius S := by
    by_cases h : S.val∈X.groups
    · simpa only [X.branch,Set.mem_ofPred_eq,radius,dite_eq_left h] using
        X.intrinsic ⟨S.val,h⟩ x (by simpa only [X.branch,Set.mem_ofPred_eq] using hx) y (by simpa only [X.branch,Set.mem_ofPred_eq] using hy)
    · simpa only [Y.branch,Set.mem_ofPred_eq,radius,dite_eq_right h] using
        Y.intrinsic ⟨S.val,memY S h⟩ x (by simpa only [Y.branch,Set.mem_ofPred_eq] using hx) y (by simpa only [Y.branch,Set.mem_ofPred_eq] using hy)
  have rad0 (S : {S // S∈P}) : 0≤radius S := by
    dsimp [radius];split <;> first | exact X.radius_nonneg _ | exact Y.radius_nonneg _
  have radU (S : {S // S∈P}) : radius S≤U := by
    dsimp [radius];split <;> first | exact X.radius_le _ | exact Y.radius_le _
  let F : ClusterFamily (I:={S // S∈P}) G w U := {
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
      exact Finset.disjoint_left.mp (hdis S.val Z.val S.property Z.property
        (fun he => hne (Subtype.ext he))) hi hj
    connected := by
      intro S x hx y hy
      obtain ⟨p,hp,hpw⟩ := walks S x hx y hy
      exact ⟨p,hp,hpw.trans (radU S)⟩ }
  refine ⟨P,F,fun _ => rfl,radius,rad0,radU,walks,?_⟩
  intro S
  dsimp [radius]
  split
  · simpa only [add_comm] using X.paid ⟨S.val,‹S.val∈X.groups›⟩
  · simpa only [add_comm] using Y.paid ⟨S.val,memY S ‹S.val∉X.groups›⟩

 theorem merge_groups
    (X Y : OriginalPaidRootFamily (B:=B) C hA hT H hH credit c reserve U)
    (cross : ∀ S∈X.groups,∀ Z∈Y.groups,Disjoint S Z) :
    (X.merge Y cross).groups=X.groups∪Y.groups := rfl

end OriginalPaidRootFamily
end MinorFreeSpanners
