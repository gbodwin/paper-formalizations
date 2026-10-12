import MinorFreeSpanners.CanonicalFreshPaidPhase
import MinorFreeSpanners.RetainedHistoryStep

/-! A literal canonical phase advances an actual finite state and its entire
previous internal tree-edge history. No phase ledger or freshness oracle is supplied. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem canonical_history_step {V : Type*} [Fintype V]
    {A B T G : SimpleGraph V} {w : Sym2 V → ℝ}
    (t r h : ℕ) (u : ℝ) (ht : 4096≤t) (hu : 1≤u) (hr : 1≤r) (hh : 0<h)
    (S : FiniteScaleState A w (200*u) (canonicalPhaseCredit t r h) u)
    (hA : A≤G) (hB : B≤G) (hT : T≤G) (hTconn : T.Connected)
    (hunit : ∀ e∈T.edgeSet,w e=1) (hfree : CliqueMinorFree G h)
    (hG : WeightedGirthAbove G w (2*(r:ℝ)*(1+2000/(t:ℝ))))
    (hw : ∀ e∈G.edgeSet,0≤w e)
    (hlight : ∀ e∈A.edgeSet,w e<(t:ℝ)*u)
    (hheavy : ∀ e∈B.edgeSet,(t:ℝ)*u≤w e)
    (hweight : ∀ e∈B.edgeSet,w e≤2*(t:ℝ)*u)
    (earlier : Finset (Sym2 V)) (hearlierT : ∀ e∈earlier,e∈T.edgeSet)
    (hearlier : ∀ e∈earlier,∃ i x y,x∈S.family.branch i ∧ y∈S.family.branch i ∧ e=s(x,y)) :
    ∃ next : FiniteScaleState G w (200*((t:ℝ)*u)) (canonicalPhaseCredit t r h) ((t:ℝ)*u),
    ∃ injection : ℝ,0≤ injection ∧ injection≤10*canonicalPhaseCredit t r h*(2*(t:ℝ)*u) ∧
    ∃ current : Finset (Sym2 V),Disjoint earlier current ∧ (∀ e∈earlier∪current,e∈T.edgeSet) ∧
      (∀ i,∃ j,S.family.branch i⊆next.family.branch j) ∧
      (∀ e∈earlier∪current,∃ j x y,x∈next.family.branch j ∧ y∈next.family.branch j ∧ e=s(x,y)) ∧
      (∑ e∈B.edgeFinset,w e)+(∑ j,next.credit j)≤(∑ i,S.credit i)+injection+
        canonicalPhaseCredit t r h*(∑ e∈current,w e) := by
  have hc : 0≤canonicalPhaseCredit t r h := by unfold canonicalPhaseCredit;positivity
  have ht1 : (1:ℝ)≤t := by exact_mod_cast (show 1≤t by omega)
  have hnext : 1≤(t:ℝ)*u := by nlinarith only [ht1,hu]
  obtain ⟨injection,hi,hbound,prior,hpaid⟩ := canonical_fresh_paid_phase t r h u ht hu hr hh
    S.family S.cover hA hB hT hTconn hunit hfree hG hw hlight hheavy hweight
    S.radius S.credit S.radius_one S.radius_cap S.intrinsic S.credit_radius S.credit_baseline
  obtain ⟨next,current,hdis,hT',hcoarse,hint,hledger⟩ := fresh_retained_phase_to_history_step
    S.family prior earlier hc (by linarith only [hnext]) hnext hearlierT hearlier hpaid
  exact ⟨next,injection,hi,hbound,current,hdis,hT',hcoarse,hint,hledger⟩

end MinorFreeSpanners
