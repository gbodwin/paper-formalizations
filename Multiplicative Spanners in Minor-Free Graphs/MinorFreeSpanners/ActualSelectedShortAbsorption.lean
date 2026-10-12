import MinorFreeSpanners.PaidShortPhaseOutput
import MinorFreeSpanners.SelectedRootBudget
import MinorFreeSpanners.ActualSelectedPhaseAssembly
import MinorFreeSpanners.SelectedResidualMaximality

/-! All four earlier root selections internally supply the same short
absorption instance, original spending certificate, mixed-tree maximality and
actual high/weak reserve provenance. Numerical compatibility and the empty-root
case remain explicit; this is not yet the later global lightness theorem. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem exists_actual_selected_short_absorption {I V : Type*} [Fintype I] [Fintype V]
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
    (Nsmall : ℕ) (future : ℝ)
    (hshortSize : 2*L≤Nsmall*b)
    (hweakReserve : Nsmall*((q:ℝ)*M)+future≤c*b/2)
    (hhighReserve : c*(4*(D+M)+D)+Nsmall*((q:ℝ)*M)+future≤R) :
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
    ∃ branch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i},
      (P∪Q).Nonempty → PaidShortPhaseOutput (B:=B) C hA hT (P∪Q) F branch K
        d credit credit radius keep L c (selectedRootHigh (P∪Q) (originalHighRoots P Q))
        (fun _ => H) (fun _ => hH) (fun _ => future) := by
  classical
  obtain ⟨P,Q,H,hH,F,keep,radius,K,hbranch,hrad,hpaths,hkeepWeak,hsub,hkeepHigh,hdeg,hforest,
    hKsub,hKtree,hKres,hbranchMax,harmMax,hcycleMax,hledger⟩ :=
    exists_actual_selected_phase_assembly C hcover hA hB hT hTconn hunit hD hM hell
      hweight hG hw hlight hheavy hg hbudget r h hr hh hfree hgeometry d credit hd1 hdD hdiam
      L c b R q s N hc hb hcred hbase hreserve hhighpay hLD hsize hbranchCost harmCost harmRoom
      hsmall hlarge hcyclePay
  obtain ⟨branch,hKsub⟩ := hKsub
  refine ⟨P,Q,H,hH,F,keep,radius,K,hbranch,hrad,hpaths,hkeepWeak,hsub,hkeepHigh,hdeg,hforest,
    ⟨branch,hKsub⟩,hKtree,hKres,hbranchMax,harmMax,hcycleMax,hledger,branch,?_⟩
  intro hnonempty
  let high := originalHighRoots P Q
  let spare : {r // r∈selectedRoots (P∪Q)} → ℝ := fun r =>
    selectedResidualCredit (P∪Q) keep credit r.val-c*(mixedEffectiveDiameter d radius r.val-1)
  have hreserveRoot := selected_root_spare_budget (P∪Q) high d keep radius credit
    c (c*b/2) R (4*(D+M)+D) (Nsmall*((q:ℝ)*M)) future
    (fun S hS => hkeepWeak S (fun h => hS ((mem_originalHighRoots P Q S).mpr h)))
    (fun S hS => ⟨(hkeepHigh S ((mem_originalHighRoots P Q S).mp hS)).2.1,
      (hkeepHigh S ((mem_originalHighRoots P Q S).mp hS)).2.2⟩)
    hweakReserve hhighReserve
  have hprior := selected_prior_bill_reindex C (P∪Q) F branch high
    (selectedResidualCredit (P∪Q) keep credit)
    ((∑ i,credit i)+c*(∑ e∈C.connectorPool hA hT (fun _ => H) (fun _ => hH)
      (fun S : {S // S∈P∪Q} => S.val),w e)) hledger
  have hconn : ConnectedWithin K Finset.univ := by
    intro i _ j _
    obtain ⟨p⟩ := hKtree.connected.preconnected i j
    exact ⟨p,by simp⟩
  have hmax : ∀ W : Finset (SelectedResidualIndex (P∪Q)),ConnectedWithin K W →
      W⊆Finset.univ\selectedRoots (P∪Q) →
      (∃ x y,∃ p : K.Walk x y,p.IsPath ∧ (∀ i∈p.support,i∈W) ∧
        L≤pathMass (mixedEffectiveDiameter d radius) p) →
          ∀ i∈W,((K.neighborFinset i)∩W).card≤2 := by
    intro W hW hR hl
    exact selected_residual_branching_maximality (P∪Q) K H hKres d radius L hbranchMax W hW
      (fun i hi => (Finset.mem_sdiff.mp (hR hi)).2) hl
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
  exact paid_short_phase_output_of_inputs C hcover hA hB hT hunit (P∪Q) hnonempty F branch
    d credit radius keep hrad hdiam hpaths K hKsub hconn hKtree.isAcyclic L c b M
    spare (fun _ => future) Nsmall q (by linarith only [hLD,hD]) hc hM hd1 hmax
    (fun i _ => hcred i) (fun i _ => hbase i) (fun i hi => (hdeg i hi).le) hweight hloop hsingle
    hshortSize (by nlinarith only [harmCost,mul_nonneg (Nat.cast_nonneg q) hM]) hreserveRoot
    (selectedRootHigh (P∪Q) high) (fun _ => H) (fun _ => hH) credit
    (fun e he => hw e (edgeSet_mono hB he)) (fun _ => by dsimp only [spare];exact le_of_eq (by ring)) hprior

end MinorFreeSpanners
