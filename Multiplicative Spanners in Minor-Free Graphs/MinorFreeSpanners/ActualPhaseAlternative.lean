import MinorFreeSpanners.ActualRetainedPhase
import MinorFreeSpanners.EmptySelectedTree

/-! An honest alternative for one actual phase: either it constructs the
paid next family, or it returns the original full residual tree together with
all three maximality exclusions and the low-degree bound. Empty selection is
not treated as a paid phase or discarded. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

noncomputable def UnselectedPhaseCertificate {I V : Type*} [Fintype I]
    {A : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I:=I) A w D) (B T : SimpleGraph V) (d : I → ℝ) (L : ℝ) (q : ℕ) : Prop :=
  ∃ H : SimpleGraph I,H≤C.graph T ∧ H.IsTree ∧
    (∀ i,(C.graph B).degree i<q) ∧
    (∀ W : Finset I,ConnectedWithin H W →
      (∃ i j,∃ p : H.Walk i j,p.IsPath ∧ (∀ v∈p.support,v∈W) ∧
        L≤pathMass (fun i => d i+1) p) → ∀ i∈W,((H.neighborFinset i)∩W).card≤2) ∧
    (∀ S : Finset I,¬C.FourArmCore H d L B S) ∧
    (∀ S : Finset I,¬C.ShortCycleCore H d L B S)

attribute [-instance] instDecidableEqSum in
 theorem actual_retained_phase_alternative {I V : Type*} [Fintype I] [Fintype V]
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
    UnselectedPhaseCertificate C B T d L q ∨
      ∃ prior : Finset (Sym2 V),FiniteRetainedPhaseOutput C G T B
        (max ((max (4*(D+M)+D) (2*(L+2*D+1)+M)+2*L)+4*(2*L+(D+1))+2*M)
          (2*L+(D+1)-1)) c baseline (∑ i,credit i) prior := by
  classical
  obtain ⟨P,Q,H,hH,F,keep,radius,K,hfloor,hbranch,hrad,hpaths,hkeepWeak,hsub,hkeepHigh,
    hdeg,hforest,hKsub,hKtree,hKres,hbranchMax,harmMax,hcycleMax,hledger,hout⟩ :=
    exists_actual_retained_phase C hcover hA hB hT hTconn hunit hD hM hell
      hweight hG hw hlight hheavy hg hbudget r h hr hh hfree hgeometry d credit hd1 hdD hdiam
      L c b R q s N hc hb hcred hbase hreserve hhighpay hLD hsize hbranchCost harmCost harmRoom
      hsmall hlarge hcyclePay Nsmall Nheavy hshortSize hweakReserve hhighReserve
      baseline hbaseline hfloorWeak hfloorHigh hheavySize hdonor hheavyCost
  by_cases hn : (P∪Q).Nonempty
  · exact Or.inr (hout hn)
  · have he : P∪Q=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    left
    refine ⟨H,hH,original_tree_of_empty_selected (P∪Q) H K he hKtree hforest hKres,?_,?_,?_,?_⟩
    · intro i
      exact hdeg i (by simp [he])
    · intro W hW hp
      exact hbranchMax W hW (by simp [he]) hp
    · intro S
      exact harmMax S (by simp [he])
    · intro S
      exact hcycleMax S (by simp [he])

end MinorFreeSpanners
