import MinorFreeSpanners.IndexedHighDegreePhase
import MinorFreeSpanners.ActualWeakRadiusFloor
import MinorFreeSpanners.SelectedSpendingRadiusFloor
import MinorFreeSpanners.SelectedResidualDegree

/-! A single actual call chain: high-degree selection, three weak phases on
the remaining old labels, original-credit pooling and the common mixed tree.
The actual common radius floor is retained with every phase ledger.
Numerical scale hypotheses and later absorption/hierarchy remain explicit. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem exists_actual_selected_phase_assembly_with_floor {I V : Type*} [Fintype I] [Fintype V]
    {A B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D M ell g : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hcover : ∀ x,∃ i,x∈C.branch i)
    (hA : A≤G) (hB : B≤G) (hT : T≤G) (hTconn : T.Connected)
    (hunit : ∀ e∈T.edgeSet,w e=1) (hD : 0≤D) (hM : 0≤M) (hell : 1<ell)
    (hweight : ∀ e∈B.edgeSet,w e≤M) (hG : WeightedGirthAbove G w g)
    (hw : ∀ e∈G.edgeSet,0≤w e) (hlight : ∀ e∈A.edgeSet,w e<ell)
    (hheavy : ∀ e∈B.edgeSet,ell≤w e) (hg : 2≤g) (hbudget : 2*D≤(g-2)*ell)
    (r h : ℕ) (hr : 1≤r) (hh : 0<h) (hfree : CliqueMinorFree G h)
    (hgeometry : ((2*r:ℕ):ℝ)*(1+D/ell)≤g)
    (d credit : I → ℝ) (hd1 : ∀ i,1≤d i) (hdD : ∀ i,d i≤D)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : A.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (L c b R : ℝ) (q s N : ℕ) (hc : 0≤c) (hb : 0≤b)
    (hcred : ∀ i,c*d i≤credit i) (hbase : ∀ i,c*b≤credit i)
    (hreserve : 2*R≤(q+1:ℕ)*(c*b))
    (hhighpay : 2*(2*fullDensityLoss h*(h:ℝ)^(2/(r+1:ℝ)))*M≤c*b)
    (hLD : 3*(D+1)<L) (hsize : L+D≤s*b)
    (hbranchCost : (s+1:ℕ)*((q:ℝ)*M)≤c*b/2)
    (harmCost : 8*((q:ℝ)*M)≤c*b) (harmRoom : 15*D+4*M+15+2*b≤6*L)
    (hsmall : ((q:ℝ)*M)*N+c*b/2≤c*((g-2)*ell-6*D-4))
    (hlarge : 2*c*(2*(L+2*D+1)+M)+c*b≤N*(c*b)) (hcyclePay : 2*((q:ℝ)*M)≤c*b)
    (floor : ℝ) (hfloorWeak : floor≤L-1) (hfloorHigh : floor≤4*(D+M)+D) :
    ∃ P Q : Finset (Finset I),∃ H : SimpleGraph I,∃ hH : H≤C.graph T,
    ∃ F : ClusterFamily (I:={S // S∈P∪Q}) G w (max (4*(D+M)+D) (2*(L+2*D+1)+M)),
    ∃ keep radius : {S // S∈P∪Q} → ℝ,∃ K : SimpleGraph (SelectedResidualIndex (P∪Q)),
      (∀ S,floor≤radius S) ∧
      (∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i}) ∧
      (∀ S,0≤radius S ∧ radius S≤max (4*(D+M)+D) (2*(L+2*D+1)+M)) ∧
      (∀ S x,x∈F.branch S → ∀ y,y∈F.branch S →
        ∃ p : G.Walk x y,(∀ z∈p.support,z∈F.branch S) ∧ walkWeight w p≤radius S) ∧
      (∀ S,S.val∉P → keep S=c*radius S+c*b/2) ∧
      (∀ S∈Q,S⊆Finset.univ\P.biUnion id) ∧
      (∀ S,(hS : S.val∈P) → keep S=(∑ i∈S.val,credit i)/2 ∧ R≤keep S ∧ radius S=4*(D+M)+D) ∧
      (∀ i,i∉(P∪Q).biUnion id → (C.graph B).degree i<q) ∧
      H.IsAcyclic ∧
      (∃ branch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i},
        K≤(C.selectedResidual hA (P∪Q) F branch).graph T) ∧ K.IsTree ∧
      (∀ i j : {i // i∉(P∪Q).biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val) ∧
      (∀ W : Finset I,ConnectedWithin H W → Disjoint W ((P∪Q).biUnion id) →
        (∃ i j,∃ p : H.Walk i j,p.IsPath ∧ (∀ v∈p.support,v∈W) ∧
          L≤pathMass (fun i => d i+1) p) → ∀ i∈W,((H.neighborFinset i)∩W).card≤2) ∧
      (∀ S : Finset I,Disjoint S ((P∪Q).biUnion id) → ¬C.FourArmCore H d L B S) ∧
      (∀ S : Finset I,Disjoint S ((P∪Q).biUnion id) → ¬C.ShortCycleCore H d L B S) ∧
      (∑ e∈C.touchingEdges B (originalMixedLabels (P∪Q) (weakRootPrior (P∪Q) (originalHighRoots P Q))),w e)+
        (∑ e∈C.markedEdges B ((P∪Q).biUnion id\originalMixedLabels (P∪Q)
          (weakRootPrior (P∪Q) (originalHighRoots P Q))),w e)+
        (∑ i,selectedResidualCredit (P∪Q) keep credit i)≤
          (∑ i,credit i)+c*(∑ e∈C.connectorPool hA hT (fun _ => H) (fun _ => hH)
            (fun S : {S // S∈P∪Q} => S.val),w e) := by
  classical
  obtain ⟨P,Fp,hpbranch,hdeg,hreserveP,hhigh⟩ := exists_indexed_high_degree_phase C hA hB hD hM
    (by linarith) hweight hG hw hlight hheavy r h hr hh hfree hgeometry q credit (c*b) R
    (mul_nonneg hc hb) hbase hreserve hhighpay
  let R₀ := Finset.univ\P.biUnion id
  obtain ⟨H,hH,weak,hweakFloor,hforest,hreach,hsub,hbranchMax,harmMax,hcycleMax⟩ :=
    exists_actual_weak_phase_sequence_with_floor C hcover hA hB hT hunit R₀ d credit hd1 hdD hdiam
      L c b M q s N hD hc hM hLD hsize hbranchCost harmCost harmRoom
      (fun i _ => hcred i) (fun i _ => hbase i)
      (fun i hi => (hdeg i (Finset.mem_sdiff.mp hi).2).le) hweight
      g ell hG hw hell hg hlight hheavy hbudget hsmall hlarge hcyclePay
  have cross : ∀ S∈P,∀ Z∈weak.groups,Disjoint S Z := by
    intro S hS Z hZ
    exact residual_group_cross P Finset.univ S Z hS (hsub Z hZ)
  obtain ⟨F,keep,radius,hfloor,hbranch,hrad,hpaths,hkeepHigh,hkeepWeak,hledger⟩ := C.combine_selected_phase_spending_with_floor hA hT P Fp hpbranch
    H hH credit c (c*b/2) weak floor hfloorHigh (fun S => hfloorWeak.trans (hweakFloor S)) cross (by linarith) hc (fun e he => by rw [hunit e he];norm_num)
    (fun e he => hw e (edgeSet_mono hB he)) hhigh
  have incP : P.biUnion id⊆(P∪weak.groups).biUnion id :=
    Finset.biUnion_subset_biUnion_of_subset_left _ Finset.subset_union_left
  have incQ : weak.groups.biUnion id⊆(P∪weak.groups).biUnion id :=
    Finset.biUnion_subset_biUnion_of_subset_left _ Finset.subset_union_right
  have residual (i : I) (hi : i∉(P∪weak.groups).biUnion id) : i∈R₀ :=
    Finset.mem_sdiff.mpr ⟨mem_univ i,fun hp => hi (incP hp)⟩
  obtain ⟨K,hK,hKtree,hKres⟩ := C.exists_selected_common_tree hA hcover hTconn (R₀:Set I)
    H hH hforest hreach (P∪weak.groups) F hbranch residual
  refine ⟨P,weak.groups,H,hH,F,keep,radius,K,hfloor,hbranch,hrad,hpaths,hkeepWeak,hsub,?_,?_,hforest,⟨hbranch,hK⟩,hKtree,hKres,?_,?_,?_,hledger⟩
  · intro S hS
    have hk := hkeepHigh S hS
    exact ⟨hk.1,(by rw [hk.1];exact (hreserveP ⟨S.val,hS⟩).2),hk.2⟩
  · intro i hi
    exact hdeg i (fun hp => hi (incP hp))
  · intro W hW hd hp
    exact hbranchMax W hW (hd.mono_right incQ) hp
  · intro S hd
    exact harmMax S (fun i hi => residual i (fun hp => Finset.disjoint_left.mp hd hi hp)) (hd.mono_right incQ)
  · intro S hd
    exact hcycleMax S (fun i hi => residual i (fun hp => Finset.disjoint_left.mp hd hi hp)) (hd.mono_right incQ)

end MinorFreeSpanners
