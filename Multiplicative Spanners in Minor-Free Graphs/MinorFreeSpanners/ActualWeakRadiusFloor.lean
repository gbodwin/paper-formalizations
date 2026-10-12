import MinorFreeSpanners.ActualWeakPhaseSequence
import MinorFreeSpanners.OriginalRootRadiusFloor

/-! Preserve the radius floor established by each of the actual branching,
four-arm and short-cycle selections on their successive residual sets. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem exists_actual_weak_phase_sequence_with_floor {I V : Type*} [Fintype I] [Fintype V]
    {A B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I := I) A w D) (hcover : ∀ x,∃ i,x∈C.branch i)
    (hA : A≤G) (hB : B≤G) (hT : T≤G) (hunit : ∀ e∈T.edgeSet,w e=1)
    (R : Finset I) (d credit : I → ℝ) (hd1 : ∀ i,1≤d i) (hdD : ∀ i,d i≤D)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : A.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (L c b M : ℝ) (q s N : ℕ) (hD : 0≤D) (hc : 0≤c) (hM : 0≤M)
    (hLD : 3*(D+1)<L) (hsize : L+D≤s*b)
    (hbranchCost : (s+1:ℕ)*((q:ℝ)*M)≤c*b/2)
    (harmCost : 8*((q:ℝ)*M)≤c*b) (harmRoom : 15*D+4*M+15+2*b≤6*L)
    (hcred : ∀ i∈R,c*d i≤credit i) (hbase : ∀ i∈R,c*b≤credit i)
    (hdeg : ∀ i∈R,(C.graph B).degree i≤q) (hweight : ∀ e∈B.edgeSet,w e≤M)
    (g ell : ℝ) (hG : WeightedGirthAbove G w g) (hw : ∀ e∈G.edgeSet,0≤w e)
    (hell : 1<ell) (hg : 2≤g) (hlight : ∀ e∈A.edgeSet,w e<ell)
    (hheavy : ∀ e∈B.edgeSet,ell≤w e) (hbudget : 2*D≤(g-2)*ell)
    (hsmall : ((q:ℝ)*M)*N+c*b/2≤c*((g-2)*ell-6*D-4))
    (hlarge : 2*c*(2*(L+2*D+1)+M)+c*b≤N*(c*b))
    (hcyclePay : 2*((q:ℝ)*M)≤c*b) :
    ∃ H : SimpleGraph I,∃ hH : H≤C.graph T,
    ∃ F : OriginalPaidRootFamily (B:=B) C hA hT H hH credit c (c*b/2) (2*(L+2*D+1)+M),
      (∀ S,L-1≤F.radius S) ∧
      H.IsAcyclic ∧ H.Reachable=(withinVertices (C.graph T) (R:Set I)).Reachable ∧
      (∀ S∈F.groups,S⊆R) ∧
      (∀ W : Finset I,ConnectedWithin H W → Disjoint W (F.groups.biUnion id) →
        (∃ i j,∃ p : H.Walk i j,p.IsPath ∧ (∀ v∈p.support,v∈W) ∧
          L≤pathMass (fun i => d i+1) p) → ∀ i∈W,((H.neighborFinset i)∩W).card≤2) ∧
      (∀ S : Finset I,S⊆R → Disjoint S (F.groups.biUnion id) → ¬C.FourArmCore H d L B S) ∧
      (∀ S : Finset I,S⊆R → Disjoint S (F.groups.biUnion id) → ¬C.ShortCycleCore H d L B S) := by
  classical
  obtain ⟨H,hH,P,F,radius,hacyc,hreach,hsub,hdis,hbranch,hrad,hpaths,_,hpaid,_,hmax⟩ :=
    exists_weighted_branching_phase C hcover hA hB hT hunit R d credit hd1 hdD hdiam
      L c b M q s hD hc hM hLD hsize hbranchCost hcred hbase hdeg hweight
      g ell hG hw (by linarith) hg hlight hheavy hbudget
  let R₁ := R\P.biUnion id
  have sub₁ : R₁⊆R := Finset.sdiff_subset
  obtain ⟨Q,Fq,hqcore,hqdis,hqbranch,_,hqpaid,_,hqmax⟩ :=
    exists_weighted_four_arm_phase C hcover hA hB hT H hH hunit R₁ d credit hd1 hdD hdiam
      L c b M q hD hc hM harmCost harmRoom
      (fun i hi => hcred i (sub₁ hi)) (fun i hi => hbase i (sub₁ hi))
      (fun i hi => hdeg i (sub₁ hi)) hweight g ell hG hw (by linarith) hg hlight hheavy hbudget
  let R₂ := R₁\Q.biUnion id
  have sub₂ : R₂⊆R := Finset.sdiff_subset.trans sub₁
  obtain ⟨Z,Fz,rz,hzcore,hzdis,hzbranch,hzrad,hzpaths,_,hzpaid,_,hzmax⟩ :=
    exists_weighted_short_cycle_phase C hcover hA hB hT H hH hunit R₂ d credit hd1 hdD hdiam
      L c b M q N hD hc hM
      (fun i hi => hcred i (sub₂ hi)) (fun i hi => hbase i (sub₂ hi))
      (fun i hi => hdeg i (sub₂ hi)) hweight g ell hG hw hell hg hlight hheavy hbudget hsmall hlarge hcyclePay
  let X : OriginalPaidRootFamily (B:=B) C hA hT H hH credit c (c*b/2) (2*(L+2*D+1)+M) :=
    .ofPhase P F hbranch radius (fun S => (hrad S).1)
      (fun S => by have h := (hrad S).2.2;linarith) hpaths (fun S => by linarith [hpaid S])
  let Y : OriginalPaidRootFamily (B:=B) C hA hT H hH credit c (c*b/2) (2*(L+2*D+1)+M) :=
    .ofPhase Q Fq hqbranch (fun _ => 2*(L+D)+M) (fun _ => by linarith)
      (fun _ => by linarith) Fq.connected (fun S => by linarith [hqpaid S])
  let Zf : OriginalPaidRootFamily (B:=B) C hA hT H hH credit c (c*b/2) (2*(L+2*D+1)+M) :=
    .ofPhase Z Fz hzbranch rz (fun S => by have h := (hzrad S).1;linarith)
      (fun S => (hzrad S).2) hzpaths (fun S => by linarith [hzpaid S])
  have xy : ∀ S∈X.groups,∀ U∈Y.groups,Disjoint S U := by
    intro S hS U hU
    exact residual_group_cross P R S U hS (hqcore U hU).1
  let XY := X.merge Y xy
  have xyz : ∀ S∈XY.groups,∀ U∈Zf.groups,Disjoint S U := by
    intro S hS U hU
    rcases Finset.mem_union.mp hS with hS|hS
    · exact residual_group_cross P R S U hS ((hzcore U hU).1.trans Finset.sdiff_subset)
    · exact residual_group_cross Q R₁ S U hS (hzcore U hU).1
  let Out := XY.merge Zf xyz
  have groups : Out.groups=P∪Q∪Z := rfl
  have incP : P.biUnion id⊆Out.groups.biUnion id := by
    apply Finset.biUnion_subset_biUnion_of_subset_left
    rw [groups];exact (Finset.subset_union_left).trans Finset.subset_union_left
  have incQ : Q.biUnion id⊆Out.groups.biUnion id := by
    apply Finset.biUnion_subset_biUnion_of_subset_left
    rw [groups];exact (Finset.subset_union_right).trans Finset.subset_union_left
  have incZ : Z.biUnion id⊆Out.groups.biUnion id := by
    apply Finset.biUnion_subset_biUnion_of_subset_left
    rw [groups];exact Finset.subset_union_right
  have residual₁ (S : Finset I) (hs : S⊆R) (hd : Disjoint S (Out.groups.biUnion id)) : S⊆R₁ := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨hs hi,fun hp => Finset.disjoint_left.mp hd hi (incP hp)⟩
  have residual₂ (S : Finset I) (hs : S⊆R) (hd : Disjoint S (Out.groups.biUnion id)) : S⊆R₂ := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨residual₁ S hs hd hi,fun hp => Finset.disjoint_left.mp hd hi (incQ hp)⟩
  have hx : ∀ S,L-1≤X.radius S := fun S => (hrad S).2.1
  have hy : ∀ S,L-1≤Y.radius S := by
    intro S
    change L-1≤2*(L+D)+M
    linarith
  have hz : ∀ S,L-1≤Zf.radius S := by
    intro S
    change L-1≤rz S
    linarith [(hzrad S).1]
  have hout : ∀ S,L-1≤Out.radius S :=
    XY.merge_radius_floor Zf xyz (L-1) (X.merge_radius_floor Y xy (L-1) hx hy) hz
  refine ⟨H,hH,Out,hout,hacyc,hreach,?_,?_,?_,?_⟩
  · intro S hS
    rw [groups] at hS
    rcases Finset.mem_union.mp hS with hS|hS
    · rcases Finset.mem_union.mp hS with hS|hS
      · exact hsub S hS
      · exact (hqcore S hS).1.trans sub₁
    · exact (hzcore S hS).1.trans sub₂
  · intro W hW hd hp
    exact hmax W hW (hd.mono_right incP) hp
  · intro S hs hd
    exact hqmax S (residual₁ S hs hd) (hd.mono_right incQ)
  · intro S hs hd
    exact hzmax S (residual₂ S hs hd) (hd.mono_right incZ)

end MinorFreeSpanners
