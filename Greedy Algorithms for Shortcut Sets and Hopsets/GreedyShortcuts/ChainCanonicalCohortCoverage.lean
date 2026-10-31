import GreedyShortcuts.ChainCanonicalExteriorIncidence

/-! Exact fixed-step physical coverage after removing the terminal W.
These are incidence counts, not sums of alternative candidate scores or
payments across events. No useful individual cohort size is assumed. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- The physical (owner,head) incidences are reindexed exactly. Repeated
centers retain their actual distinct-source multiplicity. W is excluded
from BOTH sides, so its universal terminal cohort cannot supply this mass. -/
theorem originalCanonical_nonterminal_incidence {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (d : T.OriginalSelectorStepData H root k W U) :
    (∑ y : T.RootOwner root (d.corridor.getVert d.index),
      (T.originalCanonicalPhysicalExterior d y \ {W}).card)=
      ∑ v ∈ T.originalStepFullCut d \ {W},(T.originalOwnerCanonicalGroup d v).card := by
  classical
  have hrow : ∀ y : T.RootOwner root (d.corridor.getVert d.index),
      T.originalCanonicalPhysicalExterior d y \ {W}=
        (T.originalStepFullCut d \ {W}).filter (fun v => y ∈ T.originalOwnerCanonicalGroup d v) := by
    intro y
    ext v
    constructor
    · intro hv
      obtain ⟨hvP,hvW⟩ := Finset.mem_sdiff.mp hv
      have h := (T.mem_originalCanonicalPhysicalExterior hH d y).mp hvP
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨h.1,hvW⟩,h.2⟩
    · intro hv
      obtain ⟨hvC,hy⟩ := Finset.mem_filter.mp hv
      obtain ⟨hvCut,hvW⟩ := Finset.mem_sdiff.mp hvC
      exact Finset.mem_sdiff.mpr
        ⟨(T.mem_originalCanonicalPhysicalExterior hH d y).mpr ⟨hvCut,hy⟩,hvW⟩
  have hcard : ∀ y : T.RootOwner root (d.corridor.getVert d.index),
      (T.originalCanonicalPhysicalExterior d y \ {W}).card=
        ∑ v ∈ T.originalStepFullCut d \ {W},if y ∈ T.originalOwnerCanonicalGroup d v then 1 else 0 := by
    intro y
    rw [hrow]
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  simp_rw [hcard]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _hv
  calc
    (∑ y : T.RootOwner root (d.corridor.getVert d.index),
        if y ∈ T.originalOwnerCanonicalGroup d v then 1 else 0)=
      ∑ y ∈ T.originalOwnerCanonicalGroup d v,(1 : ℕ) := by
        rw [← Finset.sum_filter]
        congr 1
        ext y
        simp
    _ = (T.originalOwnerCanonicalGroup d v).card := by simp

/-- Every actual row contributes at least Delta-2 NONTERMINAL physical
heads: at most one nonphysical initial marker and exactly one W are lost.
This total coverage is derived, not a favorable population hypothesis. -/
theorem originalCanonical_nonterminal_coverage {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) :
    Fintype.card (T.RootOwner root (d.corridor.getVert d.index))*
        (T.distance H root W-T.distance H root U-2)≤
      ∑ v ∈ T.originalStepFullCut d \ {W},(T.originalOwnerCanonicalGroup d v).card := by
  classical
  have hrow : ∀ y : T.RootOwner root (d.corridor.getVert d.index),
      T.distance H root W-T.distance H root U-2≤
        (T.originalCanonicalPhysicalExterior d y \ {W}).card := by
    intro y
    have h := (T.originalCanonicalPhysicalExterior_W_debit hH hk hW d y).2.2
    omega
  calc
    _ = ∑ _y : T.RootOwner root (d.corridor.getVert d.index),
        (T.distance H root W-T.distance H root U-2) := by simp
    _ ≤ ∑ y : T.RootOwner root (d.corridor.getVert d.index),
        (T.originalCanonicalPhysicalExterior d y \ {W}).card := by
      apply Finset.sum_le_sum
      intro y _hy
      exact hrow y
    _ = _ := T.originalCanonical_nonterminal_incidence hH d

/-- The average bound has an attained actual center. No absolute large
cohort, long shared suffix or profitable cut is inferred at that center. -/
theorem exists_originalCanonical_nonterminal_average {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U)
    (y₀ : T.RootOwner root (d.corridor.getVert d.index))
    (hgap : 3≤T.distance H root W-T.distance H root U) :
    ∃ v ∈ T.originalStepFullCut d \ {W},
      1≤(T.originalOwnerCanonicalGroup d v).card ∧
      (∀ u ∈ T.originalStepFullCut d \ {W},
        (T.originalOwnerCanonicalGroup d u).card≤(T.originalOwnerCanonicalGroup d v).card) ∧
      Fintype.card (T.RootOwner root (d.corridor.getVert d.index))*
          (T.distance H root W-T.distance H root U-2)≤
        (T.originalStepFullCut d \ {W}).card*(T.originalOwnerCanonicalGroup d v).card := by
  classical
  let C := T.originalStepFullCut d \ {W}
  have hdebit := (T.originalCanonicalPhysicalExterior_W_debit hH hk hW d y₀).2.2
  have hpositive : 0<(T.originalCanonicalPhysicalExterior d y₀ \ {W}).card := by omega
  obtain ⟨u,hu⟩ := Finset.card_pos.mp hpositive
  obtain ⟨huPhys,huNotW⟩ := Finset.mem_sdiff.mp hu
  have hinc := (T.mem_originalCanonicalPhysicalExterior hH d y₀).mp huPhys
  have huC : u ∈ C := Finset.mem_sdiff.mpr ⟨hinc.1,huNotW⟩
  obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image C
    (fun z => (T.originalOwnerCanonicalGroup d z).card) ⟨u,huC⟩
  have hGu : 1≤(T.originalOwnerCanonicalGroup d u).card :=
    Finset.one_le_card.mpr ⟨y₀,hinc.2⟩
  have htotal := T.originalCanonical_nonterminal_coverage hH hk hW d
  have hsum : (∑ z ∈ C,(T.originalOwnerCanonicalGroup d z).card)≤
      C.card*(T.originalOwnerCanonicalGroup d v).card := by
    calc
      _ ≤ ∑ _z ∈ C,(T.originalOwnerCanonicalGroup d v).card :=
        Finset.sum_le_sum (fun z hz => hmax z hz)
      _ = _ := by simp
  exact ⟨v,hv,hGu.trans (hmax u huC),hmax,htotal.trans hsum⟩

end GreedyShortcuts.ChainDistance.Context
