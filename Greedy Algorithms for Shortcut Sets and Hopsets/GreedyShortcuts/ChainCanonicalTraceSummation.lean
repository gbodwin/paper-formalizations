import GreedyShortcuts.ChainOriginalOwnerPopulation

/-! SOURCE ONLY, UNCOMPILED. Literal recursive fixed-H trace record
budgets and actual physical non-W centers. No transition is an insertion
time and no desired history/payment/owner field is supplied. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def originalCanonicalTraceWeight {H : Finset (V × V)}
    {root : V} {k : ℕ} {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z) : ℕ :=
  match tr with
  | .nil _ => 0
  | .cons d tail => T.originalCanonicalStepWeight d+originalCanonicalTraceWeight tail

noncomputable def originalCanonicalTracePopulationLower {H : Finset (V × V)}
    {root : V} {k : ℕ} {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z) : ℕ :=
  match tr with
  | .nil _ => 0
  | .cons d tail =>
      Fintype.card (T.RootOwner root (d.corridor.getVert d.index))*
        canonicalMidpointSum (T.distance H root W-T.distance H root (T.originalStepChild d)-1)+
        originalCanonicalTracePopulationLower tail

noncomputable def originalCanonicalTraceMarkerSum {H : Finset (V × V)}
    {root : V} {k : ℕ} {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z) : ℕ :=
  match tr with
  | .nil _ => 0
  | .cons d tail =>
      canonicalMidpointSum (T.distance H root W-T.distance H root (T.originalStepChild d)-1)+
        originalCanonicalTraceMarkerSum tail

noncomputable def originalTraceNonWCenterCardSum {H : Finset (V × V)}
    {root : V} {k : ℕ} {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z) : ℕ :=
  match tr with
  | .nil _ => 0
  | .cons d tail => (T.originalStepFullCut d \ {W}).card+originalTraceNonWCenterCardSum tail

noncomputable def originalTraceNonWCenters {H : Finset (V × V)}
    {root : V} {k : ℕ} {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z) : Finset V :=
  match tr with
  | .nil _ => ∅
  | .cons d tail => (T.originalStepFullCut d \ {W}) ∪ originalTraceNonWCenters tail

theorem originalTraceNonWCenters_subset {H : Finset (V × V)}
    {root : V} {k : ℕ} {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z) :
    T.originalTraceNonWCenters tr ⊆ T.originalTraceFullRemoved tr := by
  induction tr with
  | nil W => exact Finset.Subset.refl _
  | @cons W U Z d tail ih =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hv).1
    · exact Finset.mem_union_right _ (ih hv)

/-- Actual non-W center union has no repetition between chronological
cuts. The existing full-cut/final-cone partition, not event-name counting,
puts every later center in the current child and outside the current cut. -/
theorem originalTraceNonWCenters_card {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) :
    ∀ hW : T.RootConeMaximizer H root W W,
      (T.originalTraceNonWCenters tr).card=T.originalTraceNonWCenterCardSum tr := by
  classical
  induction tr with
  | nil W => intro hW;simp [originalTraceNonWCenters,originalTraceNonWCenterCardSum]
  | @cons W U Z d tail ih =>
    intro hW
    have hU := ((T.originalSelectorStepData_facts hH hk hW d).1).2.2.1
    have hTail := (T.originalTraceFullRemoved_partition hH hk tail hU).1
    have hd : Disjoint (T.originalStepFullCut d \ {W}) (T.originalTraceNonWCenters tail) := by
      apply Finset.disjoint_left.mpr
      intro v hv htail
      have hcut := (Finset.mem_sdiff.mp hv).1
      have hremoved := T.originalTraceNonWCenters_subset tail htail
      have hchild := (Finset.mem_sdiff.mp (hTail ▸ hremoved)).1
      exact (Finset.mem_sdiff.mp hcut).2 hchild
    change ((T.originalStepFullCut d \ {W}) ∪ T.originalTraceNonWCenters tail).card=
      (T.originalStepFullCut d \ {W}).card+T.originalTraceNonWCenterCardSum tail
    rw [Finset.card_union_of_disjoint hd,ih hU]

/-- Each literal selected step removes its actual old endpoint once.
No positive rank drop is needed, and no new band is added at the final child. -/
theorem originalTraceNonWCenterCardSum_debit {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) :
    ∀ hW : T.RootConeMaximizer H root W W,
      T.originalTraceNonWCenterCardSum tr+T.originalTraceLength tr=T.originalTraceFullCutCardSum tr := by
  induction tr with
  | nil W => intro hW;rfl
  | @cons W U Z d tail ih =>
    intro hW
    have hU := ((T.originalSelectorStepData_facts hH hk hW d).1).2.2.1
    have hs := ih hU
    have hd := (T.originalCanonical_cut_W_card hH hk hW d).2
    change (T.originalStepFullCut d \ {W}).card+T.originalTraceNonWCenterCardSum tail+
      (T.originalTraceLength tail+1)=(T.originalStepFullCut d).card+T.originalTraceFullCutCardSum tail
    omega

/-- Actual step lookup witnesses show the subtracted old endpoints are
distinct physical heads, using the established pairwise-disjoint cuts. -/
theorem originalTrace_oldEndpoints_distinct {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) (hW : T.RootConeMaximizer H root W W)
    {i j : ℕ} {a b : T.OriginalTraceStepRecord H root k}
    (ha : T.originalTraceStepAt tr i=some a) (hb : T.originalTraceStepAt tr j=some b)
    (hne : i≠j) : a.1≠b.1 := by
  have hA := (T.originalTraceStepAt_geometry hH hk tr hW i a ha).1
  have hB := (T.originalTraceStepAt_geometry hH hk tr hW j b hb).1
  have haCut : a.1 ∈ T.originalTraceCutAt tr i := by
    rw [T.originalTraceCutAt_record,ha]
    exact (T.originalCanonical_cut_W_card hH hk hA a.2.2).1
  have hbCut : b.1 ∈ T.originalTraceCutAt tr j := by
    rw [T.originalTraceCutAt_record,hb]
    exact (T.originalCanonical_cut_W_card hH hk hB b.2.2).1
  intro he
  exact Finset.disjoint_left.mp (T.originalTraceCuts_pairwise_disjoint hH hk tr hW hne)
    haCut (he.symm ▸ hbCut)

/-- Additive equality FIRST, natural subtraction second. The final cone
is reserved once, and each actual removed endpoint consumes one unit.
Nil/partial/inactive-start and zero-drop traces obey the same identity. -/
theorem originalTraceNonWCenters_exact {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) (hW : T.RootConeMaximizer H root W W) :
    (T.originalTraceNonWCenters tr).card+T.originalTraceLength tr+
        (T.rootHeadCone root Z).card=(T.rootHeadCone root W).card ∧
      (T.originalTraceNonWCenters tr).card=
        (T.rootHeadCone root W).card-(T.rootHeadCone root Z).card-T.originalTraceLength tr ∧
      Disjoint (T.originalTraceNonWCenters tr) (T.rootHeadCone root Z) := by
  obtain ⟨_he,hdis,_hu,hcard,hsum⟩ := T.originalTraceFullRemoved_partition hH hk tr hW
  have hn := T.originalTraceNonWCenters_card hH hk tr hW
  have hd := T.originalTraceNonWCenterCardSum_debit hH hk tr hW
  have he : (T.originalTraceNonWCenters tr).card+T.originalTraceLength tr+
      (T.rootHeadCone root Z).card=(T.rootHeadCone root W).card := by omega
  refine ⟨he,by omega,?_⟩
  apply Finset.disjoint_left.mpr
  intro v hv hz
  exact Finset.disjoint_left.mp hdis (T.originalTraceNonWCenters_subset tr hv) hz

/-- ONE unchanged H and ONE genuine FULL cap M govern every literal
step. Summed quantities are record bounds with physical center factors,
not alternative inserted-edge gains under one cap. -/
theorem originalCanonicalTrace_record_bounds {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) (M : ℕ)
    (hcap : ∀ e ∈ candidates T.G,T.potential H-T.potential (insert e H)≤M) :
    ∀ hW : T.RootConeMaximizer H root W W,
      T.originalCanonicalTracePopulationLower tr≤T.originalCanonicalTraceWeight tr ∧
      T.originalCanonicalTraceWeight tr≤T.originalTraceNonWCenterCardSum tr*M := by
  induction tr with
  | nil W => intro hW;simp [originalCanonicalTracePopulationLower,originalCanonicalTraceWeight,originalTraceNonWCenterCardSum]
  | @cons W U Z d tail ih =>
    intro hW
    have hU := ((T.originalSelectorStepData_facts hH hk hW d).1).2.2.1
    obtain ⟨hlTail,huTail⟩ := ih hU
    have hl := T.originalCanonicalStepWeight_population_lower hH hk hW d
    have hu := T.originalCanonicalStepWeight_cap_without_W hH hW d M hcap
    constructor
    · exact Nat.add_le_add hl hlTail
    · change T.originalCanonicalStepWeight d+T.originalCanonicalTraceWeight tail≤
        ((T.originalStepFullCut d \ {W}).card+T.originalTraceNonWCenterCardSum tail)*M
      rw [Nat.add_mul]
      exact Nat.add_le_add hu huTail

/-- Optional uniform coefficient is DERIVED from actual prefix heads,
while the sharper original m_i-weighted expression stays an output. -/
theorem originalCanonicalTrace_population_coefficient {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) :
    k*T.originalCanonicalTraceMarkerSum tr≤T.originalCanonicalTracePopulationLower tr := by
  induction tr with
  | nil W => simp [originalCanonicalTraceMarkerSum,originalCanonicalTracePopulationLower]
  | @cons W U Z d tail ih =>
    have hm := (T.originalSelector_owner_population hH d).2
    change k*(canonicalMidpointSum (T.distance H root W-T.distance H root U-1)+
        T.originalCanonicalTraceMarkerSum tail)≤
      Fintype.card (T.RootOwner root (d.corridor.getVert d.index))*
        canonicalMidpointSum (T.distance H root W-T.distance H root U-1)+
        T.originalCanonicalTracePopulationLower tail
    rw [Nat.mul_add]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ hm) ih

/-- Actual finite-trace aggregate. The exact final-cone/length debit is
not an insertion-time telescope or a fresh physical budget. -/
theorem originalCanonicalTrace_sandwich {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) (hW : T.RootConeMaximizer H root W W)
    (M : ℕ) (hcap : ∀ e ∈ candidates T.G,T.potential H-T.potential (insert e H)≤M) :
    k*T.originalCanonicalTraceMarkerSum tr≤T.originalCanonicalTracePopulationLower tr ∧
      T.originalCanonicalTracePopulationLower tr≤T.originalCanonicalTraceWeight tr ∧
      T.originalCanonicalTraceWeight tr≤
        ((T.rootHeadCone root W).card-(T.rootHeadCone root Z).card-T.originalTraceLength tr)*M ∧
      (T.originalTraceNonWCenters tr).card+T.originalTraceLength tr+
        (T.rootHeadCone root Z).card=(T.rootHeadCone root W).card := by
  obtain ⟨hl,hu⟩ := T.originalCanonicalTrace_record_bounds hH hk tr M hcap hW
  obtain ⟨hadd,hsub,_hdis⟩ := T.originalTraceNonWCenters_exact hH hk tr hW
  have hn := T.originalTraceNonWCenters_card hH hk tr hW
  have hu' : T.originalCanonicalTraceWeight tr≤
      ((T.rootHeadCone root W).card-(T.rootHeadCone root Z).card-T.originalTraceLength tr)*M := by
    rw [← hsub,hn]
    exact hu
  exact ⟨T.originalCanonicalTrace_population_coefficient hH tr,hl,hu',hadd⟩

end GreedyShortcuts.ChainDistance.Context
