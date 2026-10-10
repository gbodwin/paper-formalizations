import MinorFreeSpanners.MatedStarCount
import MinorFreeSpanners.MinimumBadStarFamily

/-! Partition actual unmated bad neighboring stars by their unique crossing
leaf. This is exact incidence accounting; the local per-edge quantitative
bound still requires the separate minimum-family switching argument. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

noncomputable def unmatedBadCenters (G : SimpleGraph V) (q : ℝ)
    (C : Finset V) (L : V → Finset V) (b : V) : Finset V :=
  C.filter fun c => IsBadStarPair G L b c ∧ c ∉ matedStarCenters G q C L b

noncomputable def unmatedBadLeafCenters (G : SimpleGraph V) (q : ℝ)
    (C : Finset V) (L : V → Finset V) (b u : V) : Finset V :=
  (unmatedBadCenters G q C L b).filter fun c => G.Adj u c

/-- Every actual bad neighboring star has exactly one crossing leaf in
this star; the corresponding incidence classes exhaust all unmated ones. -/
theorem unmatedBadCenters_eq_leaf_union (G : SimpleGraph V) (q : ℝ)
    (C : Finset V) (L : V → Finset V) (b : V) :
    unmatedBadCenters G q C L b =
      (L b).biUnion fun u => unmatedBadLeafCenters G q C L b u := by
  classical
  ext c
  constructor
  · intro hc
    have hbad := (Finset.mem_filter.mp hc).2.1
    obtain ⟨u,hu,v,_,huc,_,_,_⟩ := badStarPair_unique_leaves G L hbad
    exact Finset.mem_biUnion.mpr ⟨u,hu,Finset.mem_filter.mpr ⟨hc,huc⟩⟩
  · intro hc
    obtain ⟨u,_,hc⟩ := Finset.mem_biUnion.mp hc
    exact (Finset.mem_filter.mp hc).1

/-- The unique crossing-leaf property makes different real incidence
classes disjoint, so this is an equality rather than a union bound. -/
theorem unmatedBadCenters_card (G : SimpleGraph V) (q : ℝ)
    (C : Finset V) (L : V → Finset V) (b : V) :
    (unmatedBadCenters G q C L b).card =
      ∑ u ∈ L b, (unmatedBadLeafCenters G q C L b u).card := by
  classical
  rw [unmatedBadCenters_eq_leaf_union]
  apply Finset.card_biUnion
  intro u hu v hv huv
  apply Finset.disjoint_left.mpr
  intro c huc hvc
  obtain ⟨hc,heuc⟩ := Finset.mem_filter.mp huc
  have hevc := (Finset.mem_filter.mp hvc).2
  have hbad := (Finset.mem_filter.mp hc).2.1
  obtain ⟨w,_,z,_,_,_,hunique,_⟩ := badStarPair_unique_leaves G L hbad
  exact huv (((hunique u hu).mp heuc).trans ((hunique v hv).mp hevc).symm)

end MinorFreeSpanners
