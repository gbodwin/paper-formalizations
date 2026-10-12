import MinorFreeSpanners.FreshActualPhaseAlternative
import MinorFreeSpanners.CanonicalActualPhase
import MinorFreeSpanners.FreshRetainedPhaseCapTransport
import MinorFreeSpanners.CanonicalPhaseParameterChoice

/-! Instantiate every scalar phase budget with literal geometric scales.
The same actual selection/short/long construction returns either its explicit
empty-selection certificate or a fully paid next family at the next cap and
baseline. No reserve or numerical compatibility premise is supplied. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem canonical_fresh_phase_alternative {I V : Type*} [Fintype I] [Fintype V]
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
    UnselectedPhaseCertificate C B T d (2*(t:ℝ)*u) (100*t) ∨
      ∃ prior : Finset (Sym2 V),FreshFiniteRetainedPhaseOutput C G T B
        (200*((t:ℝ)*u)) (canonicalPhaseCredit t r h) ((t:ℝ)*u) (∑ i,credit i) prior := by
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
  have hhighpay : 2*(2*fullDensityLoss h*(h:ℝ)^(2/(r+1:ℝ)))*M≤c*u := by
    dsimp [sigma,M] at hden ⊢
    nlinarith only [hden]
  have halt := fresh_actual_retained_phase_alternative C hcover hA hB hT hTconn hunit hD hM
    (by simpa only [hhalf] using hell) hweight hG hw hlight hheavy hg hparallel
    r h hr hh hfree hgeometry d credit hd1 hdD hdiam
    M c u (10*c*M) (100*t) (4*t) (20*t) hc hb hcred hbase hreserve hhighpay hLD hsize
    hbranchCost harmCost harmRoom (by simpa only [hhalf] using hsmall) hlarge hcyclePay
    (4*t) (12*t) hshortSize hweakReserve hhighReserve ((t:ℝ)*u)
    (by simpa only [hhalf] using hbaseline) (by simpa only [hhalf] using hfloorWeak)
    (by simpa only [hhalf] using hfloorHigh) hheavySize hdonor hheavyCost
  rcases halt with hempty|⟨prior,hnext⟩
  · exact Or.inl hempty
  · right
    refine ⟨prior,fresh_finite_retained_phase_output_mono_cap C prior ?_ hnext⟩
    dsimp [M] at hcap ⊢
    nlinarith only [hcap]

end MinorFreeSpanners
