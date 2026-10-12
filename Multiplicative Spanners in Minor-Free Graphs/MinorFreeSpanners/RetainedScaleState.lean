import MinorFreeSpanners.RetainedPhaseCapTransport

/-! A finite state that can be supplied to the next actual phase. The radius
floor is a valid certificate enlargement, funded by the already retained
baseline reserve. No branch, edge history or credit is changed. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

structure FiniteScaleState {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (cap c baseline : ℝ) where
  count : ℕ
  family : ClusterFamily (I:=Fin count) G w cap
  cover : ∀ x,∃ j,x∈family.branch j
  radius : Fin count → ℝ
  credit : Fin count → ℝ
  radius_one : ∀ j,1≤radius j
  radius_cap : ∀ j,radius j≤cap
  intrinsic : ∀ j x,x∈family.branch j → ∀ y,y∈family.branch j →
    ∃ p : G.Walk x y,(∀ z∈p.support,z∈family.branch j) ∧ walkWeight w p≤radius j
  credit_radius : ∀ j,c*radius j≤credit j
  credit_baseline : ∀ j,c*baseline≤credit j
  credit_nonnegative : ∀ j,0≤credit j

 theorem finite_retained_phase_to_scale_state {I V : Type*} [Fintype V]
    {A G T B : SimpleGraph V} {w : Sym2 V → ℝ} {D cap c baseline initial : ℝ}
    (C : ClusterFamily (I:=I) A w D) (prior : Finset (Sym2 V))
    (hc : 0≤c) (hcap : 1≤cap) (hbaseline : 1≤baseline)
    (hout : FiniteRetainedPhaseOutput C G T B cap c baseline initial prior) :
    ∃ S : FiniteScaleState G w cap c baseline,∃ fresh : Finset (Sym2 V),
      Disjoint prior fresh ∧ (∀ e∈prior∪fresh,e∈T.edgeSet) ∧
      (∀ i,∃ j,C.branch i⊆S.family.branch j) ∧
      (∀ e∈prior∪fresh,∃ j x y,x∈S.family.branch j ∧ y∈S.family.branch j ∧ e=s(x,y)) ∧
      (∑ e∈B.edgeFinset,w e)+(∑ j,S.credit j)≤ initial+c*(∑ e∈prior∪fresh,w e) := by
  classical
  obtain ⟨fresh,hdis,hT,n,next,radius,keep,hcover,hcoarse,hrad,hwalk,hkeep,hkeep0,hint,hledger⟩ := hout
  let S : FiniteScaleState G w cap c baseline := {
    count := n
    family := next
    cover := hcover
    radius := fun j => max (radius j) 1
    credit := keep
    radius_one := fun j => le_max_right _ _
    radius_cap := fun j => max_le (hrad j) hcap
    intrinsic := by
      intro j x hx y hy
      obtain ⟨p,hp,hw⟩ := hwalk j x hx y hy
      exact ⟨p,hp,hw.trans (le_max_left _ _)⟩
    credit_radius := fun j =>
      (mul_le_mul_of_nonneg_left (max_le_max_left (radius j) hbaseline) hc).trans (hkeep j)
    credit_baseline := fun j =>
      (mul_le_mul_of_nonneg_left (le_max_right (radius j) baseline) hc).trans (hkeep j)
    credit_nonnegative := hkeep0 }
  exact ⟨S,fresh,hdis,hT,hcoarse,hint,hledger⟩

end MinorFreeSpanners
