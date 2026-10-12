import MinorFreeSpanners.SingletonAnchorShortPhase
import MinorFreeSpanners.FreshShortToRetainedFamily

/-! Complete the artificial singleton-root short and heavy phase on the
original residual tree. The final finite family retains literal connector
freshness and charges the explicit injection R exactly once. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem singleton_anchor_retained_phase {I V : Type*} [Fintype I] [Fintype V]
    {A B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hcover : ∀ x,∃ i,x∈C.branch i)
    (hA : A≤G) (hB : B≤G) (hT : T≤G) (hunit : ∀ e∈T.edgeSet,w e=1)
    (anchor : I) (hD : 0≤D) (hDE : D≤E)
    (H : SimpleGraph I) (hH : H≤C.graph T) (hTree : H.IsTree)
    (d credit : I → ℝ) (hd1 : ∀ i,1≤d i) (hdD : ∀ i,d i≤D)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : A.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (L c b M R baseline : ℝ) (q Nsmall Nheavy : ℕ)
    (hL : 0<L) (hc : 0≤c) (hb : 0≤b) (hM : 0≤M)
    (hcredit : ∀ i,c*d i≤credit i) (hbase : ∀ i,c*b≤credit i)
    (hdeg : ∀ i,(C.graph B).degree i≤q) (hweight : ∀ e∈B.edgeSet,w e≤M)
    (hw : ∀ e∈B.edgeSet,0≤w e)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬B.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j → B.Adj x y → B.Adj u v → s(x,y)=s(u,v))
    (hmax : ∀ W : Finset I,ConnectedWithin H W →
      (∃ i j,∃ p : H.Walk i j,p.IsPath ∧ (∀ v∈p.support,v∈W) ∧
        L≤pathMass (fun i => d i+1) p) → ∀ i∈W,((H.neighborFinset i)∩W).card≤2)
    (hforbid : ∀ S : Finset I,¬C.ShortCycleCore H d L B S ∧ ¬C.FourArmCore H d L B S)
    (hshortSize : 2*L≤Nsmall*b)
    (hR : c*E+Nsmall*((q:ℝ)*M)+(2*c*M+7*(Nheavy:ℝ)*((q:ℝ)*M))≤R)
    (hbaseline : 0≤baseline) (hfloor : baseline≤E) (hblock : baseline≤L-1)
    (hheavySize : 2*(2*L+(D+1))≤Nheavy*b) (hhalf : 2*((q:ℝ)*M)≤c*b)
    (hdonor : 2*(Nheavy:ℝ)*((q:ℝ)*M)≤c*L/4)
    (hcost : (Nheavy+1:ℕ)*((q:ℝ)*M)≤c*b/2) :
    ∃ prior : Finset (Sym2 V),FreshFiniteRetainedPhaseOutput C G T B
      (max ((E+2*L)+4*(2*L+(D+1))+2*M) (2*L+(D+1)-1))
      c baseline ((∑ i,credit i)+R) prior := by
  classical
  let P : Finset (Finset I) := {{anchor}}
  let F := singletonAnchorFamily C hA anchor hDE
  let branch := singletonAnchorFamily_branch C hA anchor hDE
  let K := singletonAnchorTree H anchor
  let radius : {S // S∈P} → ℝ := fun _ => E
  let keep : {S // S∈P} → ℝ := fun _ => credit anchor+R
  let a := (q:ℝ)*M
  let spare : ℝ := 2*c*M+7*(Nheavy:ℝ)*a
  let reserve : ℝ := 2*c*M+2*(Nheavy:ℝ)*a
  have ha : 0≤a := mul_nonneg (Nat.cast_nonneg _) hM
  have hE : 0≤E := hD.trans hDE
  have hspare : 0≤spare := by dsimp [spare];positivity
  have hreserve : 0≤reserve := by dsimp [reserve];positivity
  have hshort := singleton_anchor_paid_short C hcover hA hB hT hunit anchor hDE hE H hH hTree
    d credit hd1 hdiam L c b M R spare Nsmall q hL.le hc hM hcredit hbase hdeg hweight hw
    hloop hsingle hmax hshortSize (by nlinarith only [hhalf,mul_nonneg (Nat.cast_nonneg q) hM]) hR
  have hrootbase : ∀ r : {r // r∈selectedRoots P},
      c*baseline≤c*(mixedEffectiveDiameter d radius r.val-1)+(0:ℝ) := by
    rintro ⟨r,hr⟩
    cases r with
    | inl S =>
      change c*baseline≤c*((E+1)-1)+0
      have hh := mul_le_mul_of_nonneg_left hfloor hc
      linarith only [hh]
    | inr i => simp [selectedRoots] at hr
  obtain ⟨Q,O,hQ,hout⟩ := fresh_retained_family_after_paid_short C hA hB hT hcover hunit P
    (by simp [P]) F branch K (singletonAnchorTree_isTree H anchor hTree)
    (singletonAnchorTree_subgraph C hA anchor hDE H hH) H hTree.isAcyclic
    (singletonAnchorTree_residual_adj H anchor) d credit (anchorInjectedCredit credit anchor R)
    radius keep L c b a M baseline (selectedRootHigh P Finset.univ) (fun _ => H) (fun _ => hH)
    (fun _ => spare) (fun _ => reserve) (fun _ => 0) Nheavy q hshort
    (fun S hS _ => hmax S hS) (fun S _ => hforbid S) hD hL hc hb ha hM
    (fun i => ⟨hd1 i,hdD i⟩) (fun _ => ⟨hE,le_refl E⟩) hdiam hcredit hbase
    (fun _ => hspare) (fun _ => le_refl 0) hrootbase hbaseline hblock (fun _ => hreserve)
    (fun _ _ => by dsimp [reserve];ring_nf;exact le_rfl)
    (fun _ => by dsimp [reserve,spare];ring_nf;exact le_rfl) hheavySize hhalf hdonor hcost le_rfl
    (fun i _ => hdeg i) hweight hw hloop hsingle
  exact ⟨_,by simpa only [anchorInjectedCredit_sum] using hout⟩

end MinorFreeSpanners
