import MinorFreeSpanners.OriginalHighRootIndex
import MinorFreeSpanners.OriginalPaidRootFamily

/-! Join the actual high marked-edge ledger and the actual weak-root family
in one original-group indexing. High roots keep their literal half-credit;
weak roots keep their intrinsic-radius credit and the saved half baseline. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D U W : ℝ}

 theorem combine_selected_phase_spending (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (P : Finset (Finset I))
    (F : ClusterFamily (I:={S // S∈P}) G w U)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (H : SimpleGraph I) (hH : H≤C.graph T) (credit : I → ℝ) (c reserve : ℝ)
    (weak : OriginalPaidRootFamily (B:=B) C hA hT H hH credit c reserve W)
    (cross : ∀ S∈P,∀ Z∈weak.groups,Disjoint S Z)
    (hU : 0≤U) (hc : 0≤c) (hwT : ∀ e∈T.edgeSet,0≤w e) (hwB : ∀ e∈B.edgeSet,0≤w e)
    (hhigh : (∑ e∈C.markedEdges B (P.biUnion id),w e)+
      (∑ S : {S // S∈P},(∑ i∈S.val,credit i)/2)≤∑ i∈P.biUnion id,credit i) :
    ∃ K : ClusterFamily (I:={S // S∈P∪weak.groups}) G w (max U W),
    ∃ keep radius : {S // S∈P∪weak.groups} → ℝ,
      (∀ S,K.branch S={x | ∃ i∈S.val,x∈C.branch i}) ∧
      (∀ S,0≤radius S ∧ radius S≤max U W) ∧
      (∀ S x,x∈K.branch S → ∀ y,y∈K.branch S →
        ∃ p : G.Walk x y,(∀ z∈p.support,z∈K.branch S) ∧ walkWeight w p≤radius S) ∧
      (∀ S,S.val∈P → keep S=(∑ i∈S.val,credit i)/2 ∧ radius S=U) ∧
      (∀ S,S.val∉P → keep S=c*radius S+reserve) ∧
      (∑ e∈C.touchingEdges B (originalMixedLabels (P∪weak.groups)
          (weakRootPrior (P∪weak.groups) (originalHighRoots P weak.groups))),w e)+
        (∑ e∈C.markedEdges B ((P∪weak.groups).biUnion id\originalMixedLabels (P∪weak.groups)
          (weakRootPrior (P∪weak.groups) (originalHighRoots P weak.groups))),w e)+
        (∑ i,selectedResidualCredit (P∪weak.groups) keep credit i)≤
          (∑ i,credit i)+c*(∑ e∈C.connectorPool hA hT (fun _ => H) (fun _ => hH)
            (fun S : {S // S∈P∪weak.groups} => S.val),w e) := by
  classical
  let K := C.unionOriginal P weak.groups F weak.family hbranch weak.branch cross
  have hK : ∀ S,K.branch S={x | ∃ i∈S.val,x∈C.branch i} := fun _ => rfl
  let keep : {S // S∈P∪weak.groups} → ℝ := fun S =>
    if h : S.val∈P then (∑ i∈S.val,credit i)/2
      else c*weak.radius ⟨S.val,(Finset.mem_union.mp S.property).resolve_left h⟩+reserve
  let radius : {S // S∈P∪weak.groups} → ℝ := fun S =>
    if h : S.val∈P then U else weak.radius ⟨S.val,(Finset.mem_union.mp S.property).resolve_left h⟩
  have hdis : ∀ S Z,S∈P∪weak.groups → Z∈P∪weak.groups → S≠Z → Disjoint S Z := by
    intro S Z hS hZ hne
    exact C.original_groups_disjoint K Subtype.val hK ⟨S,hS⟩ ⟨Z,hZ⟩
      (fun he => hne (congrArg Subtype.val he))
  have hP : (P : Set (Finset I)).PairwiseDisjoint id := by
    intro S hS Z hZ hne
    exact C.original_groups_disjoint F Subtype.val hbranch ⟨S,hS⟩ ⟨Z,hZ⟩
      (fun he => hne (congrArg Subtype.val he))
  have hhigh' : (∑ e∈C.markedEdges B ((originalHighRoots P weak.groups).biUnion Subtype.val),w e)+
      (∑ S∈originalHighRoots P weak.groups,keep S)≤
        ∑ S∈originalHighRoots P weak.groups,∑ i∈S.val,credit i := by
    rw [originalHighRoots_union,originalHighRoots_sum P weak.groups (fun S => ∑ i∈S,credit i)]
    have hs : (∑ S∈originalHighRoots P weak.groups,keep S)=
        ∑ S∈P,(∑ i∈S,credit i)/2 := by
      rw [←originalHighRoots_sum P weak.groups (fun S => (∑ i∈S,credit i)/2)]
      apply Finset.sum_congr rfl
      intro S hS
      exact dite_eq_left ((mem_originalHighRoots P weak.groups S).mp hS)
    have hs' := hs.trans (Finset.sum_coe_sort P (fun S => (∑ i∈S,credit i)/2)).symm
    calc
      _ = (∑ e∈C.markedEdges B (P.biUnion id),w e)+(∑ S : {S // S∈P},(∑ i∈S.val,credit i)/2) :=
        congrArg (fun z => (∑ e∈C.markedEdges B (P.biUnion id),w e)+z) hs'
      _ ≤ ∑ i∈P.biUnion id,credit i := hhigh
      _ = ∑ S∈P,∑ i∈S,credit i := Finset.sum_biUnion hP
  have hweak (S : {S // S∈P∪weak.groups}) (h : S∉originalHighRoots P weak.groups) :
      (∑ e∈C.touchingEdges B S.val,w e)+keep S≤
        (∑ i∈S.val,credit i)+c*(∑ e∈C.connectorEdges hA hT H hH S.val,w e) := by
    have hn : S.val∉P := fun hp => h ((mem_originalHighRoots P weak.groups S).mpr hp)
    dsimp [keep]
    rw [dite_eq_right hn]
    simpa only [add_assoc] using weak.paid ⟨S.val,(Finset.mem_union.mp S.property).resolve_left hn⟩
  refine ⟨K,keep,radius,hK,?_,?_,?_,?_,?_⟩
  · intro S
    dsimp [radius]
    split
    · exact ⟨hU,le_max_left _ _⟩
    · exact ⟨weak.radius_nonneg _,(weak.radius_le _).trans (le_max_right _ _)⟩
  · intro S x hx y hy
    by_cases h : S.val∈P
    · obtain ⟨p,hp,hw⟩ := F.connected ⟨S.val,h⟩ x (by simpa only [hbranch,hK] using hx)
        y (by simpa only [hbranch,hK] using hy)
      refine ⟨p,by simpa only [hbranch,hK] using hp,?_⟩
      simpa only [radius,dite_eq_left h] using hw
    · obtain ⟨p,hp,hw⟩ := weak.intrinsic ⟨S.val,(Finset.mem_union.mp S.property).resolve_left h⟩
        x (by simpa only [weak.branch,hK] using hx) y (by simpa only [weak.branch,hK] using hy)
      refine ⟨p,by simpa only [weak.branch,hK] using hp,?_⟩
      simpa only [radius,dite_eq_right h] using hw
  · intro S h
    exact ⟨dite_eq_left h,dite_eq_left h⟩
  · intro S h
    simp only [keep,radius,dite_eq_right h]
  · exact C.prior_credit_from_phase_bills hA hT (P∪weak.groups) hdis
      (originalHighRoots P weak.groups) (fun _ => H) (fun _ => hH) credit keep c hc hwT hwB hhigh' hweak

end ClusterFamily
end MinorFreeSpanners
