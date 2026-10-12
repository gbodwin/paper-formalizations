import MinorFreeSpanners.RetainedScaleState
import MinorFreeSpanners.FreshFiniteRetainedPhaseOutput
import MinorFreeSpanners.CoarsenedConnectorFreshness

/-! Carry an arbitrary earlier internal tree-edge history through the same
fresh actual phase. The phase's ledger charges only its new connectors, while
the union with the entire earlier history stays internal to the next family. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem fresh_retained_phase_to_history_step {I V : Type*} [Fintype V]
    {A G T B : SimpleGraph V} {w : Sym2 V → ℝ} {D cap c baseline initial : ℝ}
    (C : ClusterFamily (I:=I) A w D) (prior earlier : Finset (Sym2 V))
    (hc : 0≤c) (hcap : 1≤cap) (hbaseline : 1≤baseline)
    (hearlierT : ∀ e∈earlier,e∈T.edgeSet)
    (hearlier : ∀ e∈earlier,∃ i x y,x∈C.branch i ∧ y∈C.branch i ∧ e=s(x,y))
    (hout : FreshFiniteRetainedPhaseOutput C G T B cap c baseline initial prior) :
    ∃ S : FiniteScaleState G w cap c baseline,∃ current : Finset (Sym2 V),
      Disjoint earlier current ∧ (∀ e∈earlier∪current,e∈T.edgeSet) ∧
      (∀ i,∃ j,C.branch i⊆S.family.branch j) ∧
      (∀ e∈earlier∪current,∃ j x y,x∈S.family.branch j ∧ y∈S.family.branch j ∧ e=s(x,y)) ∧
      (∑ e∈B.edgeFinset,w e)+(∑ j,S.credit j)≤ initial+c*(∑ e∈current,w e) := by
  classical
  obtain ⟨fresh,hexternal,_hdis,hT,n,next,radius,keep,hcover,hcoarse,hrad,hwalk,hkeep,hkeep0,hint,hledger⟩ := hout
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
  have hdisEarlier : Disjoint earlier (prior∪fresh) := by
    apply Finset.disjoint_left.mpr
    intro f he hf
    obtain ⟨i,x,y,hx,hy,heq⟩ := hearlier f he
    exact hexternal f hf i x y hx hy heq
  have hinEarlier := internal_edges_of_coarsening C next hcoarse earlier hearlier
  refine ⟨S,prior∪fresh,hdisEarlier,?_,hcoarse,?_,hledger⟩
  · intro f hf
    rcases Finset.mem_union.mp hf with hf|hf
    · exact hearlierT f hf
    · exact hT f hf
  · intro f hf
    rcases Finset.mem_union.mp hf with hf|hf
    · exact hinEarlier f hf
    · exact hint f hf

end MinorFreeSpanners
