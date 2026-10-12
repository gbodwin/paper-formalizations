import MinorFreeSpanners.SingletonAnchorTransport
import MinorFreeSpanners.SingletonAnchorPriorLedger
import MinorFreeSpanners.PaidShortPhaseOutput
import MinorFreeSpanners.SelectedResidualMaximality

/-! Construct the paid short phase on the literal original tree when all
ordinary selections are absent. One existing label is an artificial high root,
funded by an explicit injection R. Every other old credit is unchanged. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem singleton_anchor_paid_short {I V : Type*} [Fintype I] [Fintype V]
    {A B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hcover : ∀ x,∃ i,x∈C.branch i)
    (hA : A≤G) (hB : B≤G) (hT : T≤G) (hunit : ∀ e∈T.edgeSet,w e=1)
    (anchor : I) (hDE : D≤E) (hE : 0≤E)
    (H : SimpleGraph I) (hH : H≤C.graph T) (hTree : H.IsTree)
    (d credit : I → ℝ) (hd1 : ∀ i,1≤d i)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : A.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (L c b M R future : ℝ) (N q : ℕ) (hL : 0≤L) (hc : 0≤c) (hM : 0≤M)
    (hcredit : ∀ i,c*d i≤credit i) (hbase : ∀ i,c*b≤credit i)
    (hdeg : ∀ i,(C.graph B).degree i≤q) (hweight : ∀ e∈B.edgeSet,w e≤M)
    (hw : ∀ e∈B.edgeSet,0≤w e)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬B.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j → B.Adj x y → B.Adj u v → s(x,y)=s(u,v))
    (hmax : ∀ W : Finset I,ConnectedWithin H W →
      (∃ i j,∃ p : H.Walk i j,p.IsPath ∧ (∀ v∈p.support,v∈W) ∧
        L≤pathMass (fun i => d i+1) p) → ∀ i∈W,((H.neighborFinset i)∩W).card≤2)
    (hsize : 2*L≤N*b) (hrelease : (q:ℝ)*M≤c*b)
    (hR : c*E+N*((q:ℝ)*M)+future≤R) :
    let P : Finset (Finset I) := {{anchor}}
    let F := singletonAnchorFamily C hA anchor hDE
    let branch := singletonAnchorFamily_branch C hA anchor hDE
    PaidShortPhaseOutput (B:=B) C hA hT P F branch (singletonAnchorTree H anchor)
      d credit (anchorInjectedCredit credit anchor R) (fun _ => E) (fun _ => credit anchor+R)
      L c (selectedRootHigh P Finset.univ) (fun _ => H) (fun _ => hH) (fun _ => future) := by
  classical
  dsimp only
  let P : Finset (Finset I) := {{anchor}}
  let F := singletonAnchorFamily C hA anchor hDE
  let branch := singletonAnchorFamily_branch C hA anchor hDE
  let K := singletonAnchorTree H anchor
  let radius : {S // S∈P} → ℝ := fun _ => E
  let keep : {S // S∈P} → ℝ := fun _ => credit anchor+R
  let spare : {r // r∈selectedRoots P} → ℝ := fun r =>
    selectedResidualCredit P keep credit r.val-c*(mixedEffectiveDiameter d radius r.val-1)
  have hKtree := singletonAnchorTree_isTree H anchor hTree
  have hK := singletonAnchorTree_subgraph C hA anchor hDE H hH
  have hconn : ConnectedWithin K Finset.univ := by
    intro i _ j _
    obtain ⟨p⟩ := hKtree.connected.preconnected i j
    exact ⟨p,by simp⟩
  have hmax' : ∀ W : Finset (SelectedResidualIndex P),ConnectedWithin K W →
      W⊆Finset.univ\selectedRoots P →
      (∃ x y,∃ p : K.Walk x y,p.IsPath ∧ (∀ i∈p.support,i∈W) ∧
        L≤pathMass (mixedEffectiveDiameter d radius) p) →
          ∀ i∈W,((K.neighborFinset i)∩W).card≤2 := by
    intro W hW hR hl
    exact selected_residual_branching_maximality P K H
      (singletonAnchorTree_residual_adj H anchor) d radius L (fun W hW _ => hmax W hW)
      W hW (fun i hi => (Finset.mem_sdiff.mp (hR hi)).2) hl
  have hcredit0 : 0≤credit anchor :=
    (mul_nonneg hc (by linarith only [hd1 anchor])).trans (hcredit anchor)
  have hspare : ∀ r,N*((q:ℝ)*M)+future≤spare r := by
    rintro ⟨r,hr⟩
    cases r with
    | inl S =>
      change N*((q:ℝ)*M)+future≤credit anchor+R-c*((E+1)-1)
      linarith only [hcredit0,hR]
    | inr i => simp [selectedRoots] at hr
  have hpool : 0≤c*(∑ e∈C.connectorPool hA hT (fun _ : {S // S∈P} => H)
      (fun _ => hH) Subtype.val,w e) := by
    apply mul_nonneg hc
    apply Finset.sum_nonneg
    intro e he
    rw [hunit e (C.connectorPool_mem hA hT _ _ _ he)]
    norm_num
  have hprior := (singleton_anchor_prior_ledger C anchor F branch credit R hloop).trans
    (le_add_of_nonneg_right hpool)
  exact paid_short_phase_output_of_inputs C hcover hA hB hT hunit P (by simp [P]) F branch
    d credit radius keep (fun _ => ⟨hE,le_refl E⟩) hdiam (fun S => F.connected S)
    K hK hconn hKtree.isAcyclic L c b M spare (fun _ => future) N q hL hc hM hd1 hmax'
    (fun i _ => hcredit i) (fun i _ => hbase i) (fun i _ => hdeg i) hweight hloop hsingle
    hsize hrelease hspare (selectedRootHigh P Finset.univ) (fun _ => H) (fun _ => hH)
    (anchorInjectedCredit credit anchor R) hw
    (fun _ => by dsimp only [spare];exact le_of_eq (by ring)) hprior

end MinorFreeSpanners
