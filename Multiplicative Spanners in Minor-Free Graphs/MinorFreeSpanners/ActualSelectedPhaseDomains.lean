import MinorFreeSpanners.ActualSelectedPhaseAssembly
import MinorFreeSpanners.SelectedResidualMassDomains

/-! Actual root selections, their original payment ledger and the small/long
residual geometry now share one constructed instance. Long paths are produced
internally; short components have bounded maximum path mass. Their later
partial absorption and the scale/hierarchy choices remain open. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem exists_actual_selected_phase_domains {I V : Type*} [Fintype I] [Fintype V]
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
    (hlarge : 2*c*(2*(L+2*D+1)+M)+c*b≤N*(c*b)) (hcyclePay : 2*((q:ℝ)*M)≤c*b) :
    ∃ P Q : Finset (Finset I),∃ H : SimpleGraph I,∃ hH : H≤C.graph T,
    ∃ F : ClusterFamily (I:={S // S∈P∪Q}) G w (max (4*(D+M)+D) (2*(L+2*D+1)+M)),
    ∃ keep radius : {S // S∈P∪Q} → ℝ,∃ K : SimpleGraph (SelectedResidualIndex (P∪Q)),
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
            (fun S : {S // S∈P∪Q} => S.val),w e) ∧
      ∃ U S : Finset (SelectedResidualIndex (P∪Q)),
        U⊆Finset.univ\selectedRoots (P∪Q) ∧ S⊆Finset.univ\selectedRoots (P∪Q) ∧
        Disjoint U S ∧ U∪S=Finset.univ\selectedRoots (P∪Q) ∧
        (∀ i∈U,((K.neighborFinset i)∩U).card≤2) ∧
        (∀ t : (K.induce (U:Set _)).ConnectedComponent,
          ∃ x y,∃ p : K.Walk x y,p.IsPath ∧ p.support.toFinset=ResidualComponents.block K U t ∧
            L≤pathMass (mixedEffectiveDiameter d radius) p) ∧
        (∀ t : (K.induce (S:Set _)).ConnectedComponent,
          ∀ x y,∀ p : K.Walk x y,p.IsPath →
            (∀ i∈p.support,i∈ResidualComponents.block K S t) →
              pathMass (mixedEffectiveDiameter d radius) p<L) ∧
        (∀ i∈U,∀ j∈S,¬K.Adj i j) := by
  classical
  obtain ⟨P,Q,H,hH,F,keep,radius,K,hbranch,hrad,hpaths,hkeepWeak,hsub,hkeepHigh,hdeg,hforest,
    hKsub,hKtree,hKres,hbranchMax,harmMax,hcycleMax,hledger⟩ :=
    exists_actual_selected_phase_assembly C hcover hA hB hT hTconn hunit hD hM hell
      hweight hG hw hlight hheavy hg hbudget r h hr hh hfree hgeometry d credit hd1 hdD hdiam
      L c b R q s N hc hb hcred hbase hreserve hhighpay hLD hsize hbranchCost harmCost harmRoom
      hsmall hlarge hcyclePay
  have hdomains := exists_selected_residual_mass_domains (P∪Q) K H hKtree.isAcyclic hKres d hd1 radius L hbranchMax
  exact ⟨P,Q,H,hH,F,keep,radius,K,hbranch,hrad,hpaths,hkeepWeak,hsub,hkeepHigh,hdeg,hforest,
    hKsub,hKtree,hKres,hbranchMax,harmMax,hcycleMax,hledger,hdomains⟩

end MinorFreeSpanners
