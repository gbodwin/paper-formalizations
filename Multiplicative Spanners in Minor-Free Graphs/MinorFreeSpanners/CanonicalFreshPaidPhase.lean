import MinorFreeSpanners.CanonicalFreshPhaseAlternative
import MinorFreeSpanners.SingletonAnchorRetainedPhase

/-! Every actual phase returns a fresh paid output. Empty selections are handled
by the constructed singleton short/heavy phase, with a bounded explicit injection. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem canonical_fresh_paid_phase {I V : Type*} [Fintype I] [Fintype V]
    {A B T G : SimpleGraph V} {w : Sym2 V → ℝ}
    (t r h : ℕ) (u : ℝ) (ht : 4096≤t) (hu : 1≤u) (hr : 1≤r) (hh : 0<h)
    (C : ClusterFamily (I:=I) A w (200*u)) (hcover : ∀ x,∃ i,x∈C.branch i)
    (hA : A≤G) (hB : B≤G) (hT : T≤G) (hTconn : T.Connected)
    (hunit : ∀ e∈T.edgeSet,w e=1) (hfree : CliqueMinorFree G h)
    (hG : WeightedGirthAbove G w (2*(r:ℝ)*(1+2000/(t:ℝ))))
    (hw : ∀ e∈G.edgeSet,0≤w e)
    (hlight : ∀ e∈A.edgeSet,w e<(t:ℝ)*u)
    (hheavy : ∀ e∈B.edgeSet,(t:ℝ)*u≤w e)
    (hweight : ∀ e∈B.edgeSet,w e≤2*(t:ℝ)*u)
    (d credit : I → ℝ) (hd1 : ∀ i,1≤d i) (hdD : ∀ i,d i≤200*u)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : A.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (hcred : ∀ i,canonicalPhaseCredit t r h*d i≤credit i)
    (hbase : ∀ i,canonicalPhaseCredit t r h*u≤credit i) :
    ∃ injection : ℝ,0≤ injection ∧ injection≤10*canonicalPhaseCredit t r h*(2*(t:ℝ)*u) ∧
      ∃ prior : Finset (Sym2 V),FreshFiniteRetainedPhaseOutput C G T B
        (200*((t:ℝ)*u)) (canonicalPhaseCredit t r h) ((t:ℝ)*u)
        ((∑ i,credit i)+injection) prior := by
  classical
  let sigma := fullDensityLoss h*(h:ℝ)^(2/(r+1:ℝ))
  let c := canonicalPhaseCredit t r h
  let M := 2*(t:ℝ)*u
  let g := 2*(r:ℝ)*(1+2000/(t:ℝ))
  obtain ⟨hcredit,hdenCredit⟩ := canonical_phase_credit t sigma (by omega)
  change 30000*(t:ℝ)^3≤c at hcredit
  change 8*sigma*(t:ℝ)≤c at hdenCredit
  obtain ⟨hg,hgap,hparallel,hgeometry⟩ := canonical_phase_girth t r u ht hr hu
  obtain ⟨hc,hD,hM,hb,hell,hreserve,hden,hLD,hsize,hbranchCost,harmCost,harmRoom,
    hsmall,hlarge,hcyclePay,hshortSize,hweakReserve,hhighReserve,hbaseline,hfloorWeak,
    hfloorHigh,hheavySize,hdonor,hheavyCost,hcap⟩ :=
    canonical_phase_numerics t u c sigma g ht hu hcredit hdenCredit hgap
  have hhalf : (2*(t:ℝ)*u)/2=(t:ℝ)*u := by ring
  have alt := canonical_fresh_phase_alternative t r h u ht hu hr hh C hcover
    hA hB hT hTconn hunit hfree hG hw hlight hheavy hweight d credit hd1 hdD hdiam hcred hbase
  rcases alt with hempty|⟨prior,hpaid⟩
  · obtain ⟨H,hH,hTree,hdeg,hmax,harm,hcycle⟩ := hempty
    let anchor : I := Classical.choice hTree.connected.nonempty
    let E := 4*(200*u+M)+200*u
    have hell' : 1<(t:ℝ)*u := by simpa only [hhalf] using hell
    have hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬B.Adj x y := by
      intro i x hx y hy hxy
      exact C.no_heavy_loop hA hG hw hlight (by linarith only [hg])
        (by nlinarith only [hD,hparallel,hell']) i hx hy (hB hxy) (hheavy _ hxy)
    have hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
        ∀ a,a∈C.branch i → ∀ v,v∈C.branch j → B.Adj x y → B.Adj a v → s(x,y)=s(a,v) := by
      intro i j x hx y hy a ha v hv hxy hav
      rcases le_total (w s(x,y)) (w s(a,v)) with he|he
      · exact C.heavy_edge_unique hA hG hw hlight hg hparallel i j hx hy ha hv
          (hB hxy) (hB hav) (hheavy _ hav) he
      · exact (C.heavy_edge_unique hA hG hw hlight hg hparallel i j ha hv hx hy
          (hB hav) (hB hxy) (hheavy _ hxy) he).symm
    obtain ⟨prior,hpaid⟩ := singleton_anchor_retained_phase C hcover hA hB hT hunit anchor hD
      (show 200*u≤E by dsimp [E];linarith only [hD,hM]) H hH hTree
      d credit hd1 hdD hdiam M c u M (10*c*M) ((t:ℝ)*u) (100*t) (4*t) (12*t)
      (by linarith only [hLD,hD]) hc hb hM hcred hbase (fun i => (hdeg i).le) hweight
      (fun e he => hw e (edgeSet_mono hB he)) hloop hsingle hmax
      (fun S => ⟨hcycle S,harm S⟩) hshortSize hhighReserve
      (by simpa only [hhalf] using hbaseline) (by simpa only [hhalf] using hfloorHigh)
      (by simpa only [hhalf] using hfloorWeak) hheavySize hcyclePay hdonor hheavyCost
    have hcapAnchor : max ((E+2*M)+4*(2*M+(200*u+1))+2*M) (2*M+(200*u+1)-1)≤200*((t:ℝ)*u) := by
      have hmono : max ((E+2*M)+4*(2*M+(200*u+1))+2*M) (2*M+(200*u+1)-1) ≤
          max ((max E (2*(M+2*(200*u)+1)+M)+2*M)+4*(2*M+(200*u+1))+2*M) (2*M+(200*u+1)-1) := by
        apply max_le_max _ le_rfl
        linarith only [le_max_left E (2*(M+2*(200*u)+1)+M)]
      have h := hmono.trans hcap
      dsimp [M] at h ⊢
      nlinarith only [h]
    refine ⟨10*c*M,by positivity,le_rfl,prior,?_⟩
    exact fresh_finite_retained_phase_output_mono_cap C prior hcapAnchor hpaid
  · refine ⟨0,le_rfl,by positivity,prior,?_⟩
    simpa only [add_zero] using hpaid

end MinorFreeSpanners
