import MinorFreeSpanners.ActualShortRadiusFloor
import MinorFreeSpanners.SelectedClassHeavyInputs
import MinorFreeSpanners.ShortToRetainedFamily

/-! One actual phase from the original covering family: select high roots and
all three weak classes, absorb short components, then construct the long heavy
phase and finite next family on the same witnesses. The selected radius floors
discharge the baseline premise; canonical high/weak reserves are constructed, while scalar compatibility and the nonempty-root route
remain explicit. Every original phase output is retained beside the final bill. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem exists_actual_retained_phase {I V : Type*} [Fintype I] [Fintype V]
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
    (Nsmall Nheavy : ℕ)
    (hshortSize : 2*L≤Nsmall*b)
    (hweakReserve : Nsmall*((q:ℝ)*M)+5*(Nheavy:ℝ)*((q:ℝ)*M)≤c*b/2)
    (hhighReserve : c*(4*(D+M)+D)+Nsmall*((q:ℝ)*M)+(2*c*M+7*(Nheavy:ℝ)*((q:ℝ)*M))≤R)
    (baseline : ℝ) (hbaseline : 0≤baseline)
    (hfloorWeak : baseline≤L-1) (hfloorHigh : baseline≤4*(D+M)+D)
    (hheavySize : 2*(2*L+(D+1))≤Nheavy*b)
    (hdonor : 2*(Nheavy:ℝ)*((q:ℝ)*M)≤c*L/4)
    (hheavyCost : (Nheavy+1:ℕ)*((q:ℝ)*M)≤c*b/2) :
    ∃ P Q : Finset (Finset I),∃ H : SimpleGraph I,∃ hH : H≤C.graph T,
    ∃ F : ClusterFamily (I:={S // S∈P∪Q}) G w (max (4*(D+M)+D) (2*(L+2*D+1)+M)),
    ∃ keep radius : {S // S∈P∪Q} → ℝ,∃ K : SimpleGraph (SelectedResidualIndex (P∪Q)),
      (∀ S,baseline≤radius S) ∧
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
      ((P∪Q).Nonempty → ∃ prior : Finset (Sym2 V),
        FiniteRetainedPhaseOutput C G T B
          (max ((max (4*(D+M)+D) (2*(L+2*D+1)+M)+2*L)+4*(2*L+(D+1))+2*M)
            (2*L+(D+1)-1)) c baseline (∑ i,credit i) prior) := by
  classical
  let a := (q:ℝ)*M
  let highSpare := 2*c*M+7*(Nheavy:ℝ)*a
  let weakSpare := 5*(Nheavy:ℝ)*a
  let highReserve := 2*c*M+2*(Nheavy:ℝ)*a
  let weakReserve : ℝ := 0
  let highFuture : ℝ := 0
  let weakFuture : ℝ := 0
  have ha : 0≤a := mul_nonneg (Nat.cast_nonneg _) hM
  have hsH : 0≤highSpare := by dsimp [highSpare];positivity
  have hsW : 0≤weakSpare := by dsimp [weakSpare];positivity
  have hrH : highFuture≤highReserve := by dsimp [highFuture,highReserve];positivity
  have hrW : weakFuture≤weakReserve := le_rfl
  have hattach : 2*c*M+2*(Nheavy:ℝ)*((q:ℝ)*M)+highFuture≤highReserve := by
    dsimp [highFuture,highReserve,a];ring_nf;exact le_rfl
  have hbudgetH : 5*(Nheavy:ℝ)*((q:ℝ)*M)+highReserve≤highSpare := by
    dsimp [highReserve,highSpare,a];ring_nf;exact le_rfl
  have hbudgetW : 5*(Nheavy:ℝ)*((q:ℝ)*M)+weakReserve≤weakSpare := by
    dsimp [weakReserve,weakSpare,a];ring_nf;exact le_rfl
  obtain ⟨P,Q,H,hH,F,keep,radius,K,hfloor,hbranch,hrad,hpaths,hkeepWeak,hsub,hkeepHigh,hdeg,hforest,
    hKsub,hKtree,hKres,hbranchMax,harmMax,hcycleMax,hledger,branch,hshort⟩ :=
    exists_actual_selected_class_short_absorption_with_floor C hcover hA hB hT hTconn hunit hD hM hell
      hweight hG hw hlight hheavy hg hbudget r h hr hh hfree hgeometry d credit hd1 hdD hdiam
      L c b R q s N hc hb hcred hbase hreserve hhighpay hLD hsize hbranchCost harmCost harmRoom
      hsmall hlarge hcyclePay Nsmall highSpare weakSpare hshortSize hweakReserve hhighReserve
      baseline hfloorWeak hfloorHigh
  refine ⟨P,Q,H,hH,F,keep,radius,K,hfloor,hbranch,hrad,hpaths,hkeepWeak,hsub,hkeepHigh,hdeg,hforest,
    hKsub,hKtree,hKres,hbranchMax,harmMax,hcycleMax,hledger,?_⟩
  intro hnonempty
  let high := originalHighRoots P Q
  obtain ⟨hspare0,hfuture0,hrootbase,hfuture,hattach',hrootbudget⟩ :=
    selected_class_heavy_inputs (P∪Q) high d radius baseline c M ((q:ℝ)*M) Nheavy
      highSpare weakSpare highReserve weakReserve highFuture weakFuture hc hfloor
      hsH hsW (le_refl 0) (le_refl 0) hrH hrW hattach hbudgetH hbudgetW
  have hK : K≤(C.selectedResidual hA (P∪Q) F branch).graph T := by
    obtain ⟨branch',hK⟩ := hKsub
    exact hK
  have hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬B.Adj x y := by
    intro i x hx y hy hxy
    exact C.no_heavy_loop hA hG hw hlight (by linarith only [hg]) (by nlinarith only [hD,hbudget,hell]) i hx hy
      (hB hxy) (hheavy _ hxy)
  have hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j → B.Adj x y → B.Adj u v → s(x,y)=s(u,v) := by
    intro i j x hx y hy u hu v hv hxy huv
    rcases le_total (w s(x,y)) (w s(u,v)) with he|he
    · exact C.heavy_edge_unique hA hG hw hlight hg hbudget i j hx hy hu hv
        (hB hxy) (hB huv) (hheavy _ huv) he
    · exact (C.heavy_edge_unique hA hG hw hlight hg hbudget i j hu hv hx hy
        (hB huv) (hB hxy) (hheavy _ hxy) he).symm
  obtain ⟨U,O,hU,hout⟩ := retained_family_after_paid_short C hA hB hT hcover hunit (P∪Q) hnonempty
    F branch K hKtree hK H hforest hKres d credit credit radius keep L c b ((q:ℝ)*M) M baseline
    (selectedRootHigh (P∪Q) high) (fun _ => H) (fun _ => hH)
    (selectedClassValue (P∪Q) high highSpare weakSpare)
    (selectedClassValue (P∪Q) high highReserve weakReserve)
    (selectedClassValue (P∪Q) high highFuture weakFuture) Nheavy q (hshort hnonempty) hbranchMax
    (fun S hS => ⟨hcycleMax S hS,harmMax S hS⟩)
    hD (by linarith only [hLD,hD]) hc hb (mul_nonneg (Nat.cast_nonneg _) hM) hM
    (fun i => ⟨hd1 i,hdD i⟩) hrad hdiam hcred hbase hspare0 hfuture0 hrootbase hbaseline hfloorWeak
    hfuture hattach' hrootbudget hheavySize
    (by nlinarith only [harmCost,mul_nonneg (Nat.cast_nonneg q) hM]) hdonor hheavyCost
    le_rfl (fun i hi => (hdeg i hi).le) hweight (fun e he => hw e (edgeSet_mono hB he)) hloop hsingle
  exact ⟨_,hout⟩

end MinorFreeSpanners
