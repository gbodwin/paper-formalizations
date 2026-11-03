import GreedyShortcuts.ChainActualGreedyTraceBudget

/-! SOURCE ONLY, UNCOMPILED. Actual retained-child population is an old
owner-family population at a literal relay. The FULL cap is the SAME active
raw state's selected marginal. No guard population or source minimum is
inherited, and no physical old stock is counted as fresh volume. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset DirectedPaths
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- The actual relay identity gives a real cone inclusion, not a favorable
row-population hypothesis. The exact non-W cut debit is exported alongside
the population-sensitive record bound; all selected Q/F data stay in d. -/
theorem originalRelay_retained_population_budget (D : ℕ) (hD : 2≤D)
    (S : (T.algorithm D hD).State) (hbad : ¬T.stopped D S.1)
    {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer S.1 root W W)
    (d : T.OriginalSelectorStepData S.1 root k W U)
    (hrelay : U=d.maxOwner) :
    T.rootHeadCone root U ⊆ T.rootHeadCone root (d.corridor.getVert d.index) ∧
      0<(T.rootHeadCone root U).card ∧
      (T.rootHeadCone root U).card*
          canonicalMidpointSum (T.distance S.1 root W-T.distance S.1 root U-1)≤
        (T.originalStepFullCut d \ {W}).card*
          (T.potential S.1-T.potential ((T.algorithm D hD).step S).1) ∧
      (T.originalStepFullCut d \ {W}).card+1+(T.rootHeadCone root U).card=
        (T.rootHeadCone root W).card := by
  classical
  have hVa := (T.mem_rootHeadCone_iff.mp d.ownerMaximum.1).2.1
  have hUa : Reachable T.G U (d.corridor.getVert d.index) := by
    simpa only [hrelay] using hVa
  have hsub := T.rootHeadCone_mono (root := root) hUa
  have hpop : (T.rootHeadCone root U).card≤
      Fintype.card (T.RootOwner root (d.corridor.getVert d.index)) := by
    rw [T.rootOwner_card_eq]
    exact Finset.card_le_card hsub
  have hf := (T.originalSelectorStepData_facts S.2 hk hW d).1
  have hU := hf.2.2.1
  have hchild := hf.2.2.2.1
  have hnonempty : 0<(T.rootHeadCone root U).card :=
    Finset.card_pos.mpr ⟨U,hU.1⟩
  have hlo := T.originalCanonicalStepWeight_population_lower S.2 hk hW d
  have hhi := T.originalCanonicalStepWeight_cap_without_W S.2 hW d
    (T.potential S.1-T.potential ((T.algorithm D hD).step S).1)
    (T.actualGreedyState_drop_cap D hD S hbad).2
  have hbudget := (Nat.mul_le_mul_right
    (canonicalMidpointSum (T.distance S.1 root W-T.distance S.1 root U-1)) hpop).trans
      (hlo.trans hhi)
  have hcard := Finset.card_sdiff_add_card_inter
    (T.rootHeadCone root W) (T.rootHeadCone root U)
  rw [Finset.inter_eq_right.mpr hchild] at hcard
  change (T.originalStepFullCut d).card+(T.rootHeadCone root U).card=
    (T.rootHeadCone root W).card at hcard
  have hdebit := (T.originalCanonical_cut_W_card S.2 hk hW d).2
  exact ⟨hsub,hnonempty,hbudget,by omega⟩

end GreedyShortcuts.ChainDistance.Context
