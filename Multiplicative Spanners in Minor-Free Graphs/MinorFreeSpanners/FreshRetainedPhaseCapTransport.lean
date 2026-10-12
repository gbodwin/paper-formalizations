import MinorFreeSpanners.FreshFiniteRetainedPhaseOutput

/-! Enlarge only the uniform cap of the actual next family. Its branches,
pointwise radius and credit, connector identities, and payment ledger stay fixed.
This transports the explicit numerical cap to the next geometric scale. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset

 theorem fresh_finite_retained_phase_output_mono_cap {I V : Type*} [Fintype V]
    {A G T B : SimpleGraph V} {w : Sym2 V → ℝ} {D cap cap' c baseline initial : ℝ}
    (C : ClusterFamily (I:=I) A w D) (prior : Finset (Sym2 V))
    (hcap : cap≤cap')
    (hout : FreshFiniteRetainedPhaseOutput C G T B cap c baseline initial prior) :
    FreshFiniteRetainedPhaseOutput C G T B cap' c baseline initial prior := by
  classical
  obtain ⟨fresh,hexternal,hdis,hT,n,next,radius,keep,hcover,hcoarse,hrad,hwalk,hkeep,hkeep0,hint,hledger⟩ := hout
  let next' : ClusterFamily (I:=Fin n) G w cap' := {
    branch := next.branch
    nonempty := next.nonempty
    disjoint := next.disjoint
    connected := by
      intro j x hx y hy
      obtain ⟨p,hp,hw⟩ := next.connected j x hx y hy
      exact ⟨p,hp,hw.trans hcap⟩ }
  exact ⟨fresh,hexternal,hdis,hT,n,next',radius,keep,hcover,hcoarse,
    (fun j => (hrad j).trans hcap),hwalk,hkeep,hkeep0,hint,hledger⟩

end MinorFreeSpanners
