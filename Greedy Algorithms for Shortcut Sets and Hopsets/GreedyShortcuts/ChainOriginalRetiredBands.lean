import GreedyShortcuts.ChainOriginalRankBand

/-! SOURCE ONLY, UNCOMPILED. Literal retired-band union along the SAME
actual H-fixed finite selector trace. All disjointness and cardinal bounds
are proved outputs. They count old physical heads, NOT fresh E or payment. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- The true retired portions, excluding a retained terminal anchor. The
normalization passed to the tail is DERIVED from this actual step. -/
noncomputable def originalTraceRetiredBands {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) :
    T.RootConeMaximizer H root W W → Finset V :=
  match tr with
  | .nil _ => fun _ => ∅
  | .cons d tail => fun hW =>
      T.originalStepRetiredBand hH hk hW d ∪
        originalTraceRetiredBands hH hk tail
          (T.originalSelectorStepData_facts hH hk hW d).1.2.2.1

noncomputable def originalTraceBandAnchorLoss {H : Finset (V × V)}
    {root : V} {k : ℕ} {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z) : ℕ :=
  match tr with
  | .nil _ => 0
  | .cons d tail => T.originalStepBandAnchorLoss d+originalTraceBandAnchorLoss tail

/-- Output predicate: each stage's actual retired set is disjoint from
the ENTIRE subsequent retired union, recursively. Not a trace field. -/
def originalTraceRetiredBandsDisjoint {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) :
    T.RootConeMaximizer H root W W → Prop :=
  match tr with
  | .nil _ => fun _ => True
  | .cons d tail => fun hW =>
      Disjoint (T.originalStepRetiredBand hH hk hW d)
        (T.originalTraceRetiredBands hH hk tail
          (T.originalSelectorStepData_facts hH hk hW d).1.2.2.1) ∧
      originalTraceRetiredBandsDisjoint hH hk tail
        (T.originalSelectorStepData_facts hH hk hW d).1.2.2.1

/-- Exact union/cardinality for ANY actual trace, including partial, nil
and zero-rank-drop traces. The loss counts retained anchors literally. -/
theorem originalTraceRetiredBands_facts {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) :
    ∀ hW : T.RootConeMaximizer H root W W,
      T.originalTraceRetiredBands hH hk tr hW ⊆
          T.rootHeadCone root W \ T.rootHeadCone root Z ∧
      (T.originalTraceRetiredBands hH hk tr hW).card+T.originalTraceBandAnchorLoss tr=
          T.originalTraceLength tr*(15*k+1) ∧
      T.originalTraceRetiredBandsDisjoint hH hk tr hW := by
  classical
  induction tr with
  | nil W =>
    intro hW
    simp [originalTraceRetiredBands,originalTraceBandAnchorLoss,
      originalTraceLength,originalTraceRetiredBandsDisjoint]
  | @cons W U Z d tail ih =>
    intro hW
    have hf := (T.originalSelectorStepData_facts hH hk hW d).1
    have hU := hf.2.2.1
    have hUW := hf.2.2.2.1
    have hZU := (T.originalTrace_bounds hH hk tail hU).2.2.1
    obtain ⟨hsubTail,hcardTail,hdisTail⟩ := ih hU
    let B := T.originalStepRetiredBand hH hk hW d
    let F := T.originalTraceRetiredBands hH hk tail hU
    have hsubB : B ⊆ T.rootHeadCone root W \ T.rootHeadCone root U :=
      T.originalStepRetiredBand_subset hH hk hW d
    have hsubF : F ⊆ T.rootHeadCone root U \ T.rootHeadCone root Z := hsubTail
    have hdis : Disjoint B F := by
      apply Finset.disjoint_left.mpr
      intro b hb hf'
      exact (Finset.mem_sdiff.mp (hsubB hb)).2 (Finset.mem_sdiff.mp (hsubF hf')).1
    have hsubUnion : B ∪ F ⊆ T.rootHeadCone root W \ T.rootHeadCone root Z := by
      intro b hb
      rcases Finset.mem_union.mp hb with hb|hb
      · obtain ⟨hp,hnot⟩ := Finset.mem_sdiff.mp (hsubB hb)
        exact Finset.mem_sdiff.mpr ⟨hp,fun hz => hnot (hZU hz)⟩
      · obtain ⟨hp,hnot⟩ := Finset.mem_sdiff.mp (hsubF hb)
        exact Finset.mem_sdiff.mpr ⟨hUW hp,hnot⟩
    have hcardB : B.card+T.originalStepBandAnchorLoss d=15*k+1 :=
      T.originalStepRetiredBand_card hH hk hW d
    have hcardF : F.card+T.originalTraceBandAnchorLoss tail=
        T.originalTraceLength tail*(15*k+1) := hcardTail
    change (B ∪ F) ⊆ T.rootHeadCone root W \ T.rootHeadCone root Z ∧
      (B ∪ F).card+(T.originalStepBandAnchorLoss d+T.originalTraceBandAnchorLoss tail)=
        (T.originalTraceLength tail+1)*(15*k+1) ∧
      Disjoint B F ∧ T.originalTraceRetiredBandsDisjoint hH hk tail hU
    refine ⟨hsubUnion,?_,hdis,hdisTail⟩
    rw [Finset.card_union_of_disjoint hdis,Nat.add_mul,Nat.one_mul]
    omega

theorem originalTraceBandAnchorLoss_zero_length {H : Finset (V × V)}
    {root : V} {k : ℕ} {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z)
    (hz : T.originalTraceLength tr=0) : T.originalTraceBandAnchorLoss tr=0 := by
  cases tr with
  | nil => rfl
  | cons d tail => simp [originalTraceLength] at hz

/-- At most ONE retained anchor over the whole trace: when it occurs the
actual next endpoint is below q and the entire subsequent trace is empty. -/
theorem originalTraceBandAnchorLoss_le_one {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) : T.originalTraceBandAnchorLoss tr≤1 := by
  classical
  induction tr with
  | nil W => simp [originalTraceBandAnchorLoss]
  | @cons W U Z d tail ih =>
    by_cases he : U=d.corridor.getVert d.index
    · have hz := (T.originalTrace_after_anchor_child hH hk d he tail).2
      have hzero := T.originalTraceBandAnchorLoss_zero_length tail hz
      simp [originalTraceBandAnchorLoss,originalStepBandAnchorLoss,he,hzero]
    · simpa [originalTraceBandAnchorLoss,originalStepBandAnchorLoss,he] using ih

/-- An OLD-cone bound, not new physical/initial/E stock or an objective
payment. The exact prior formula retains the possible one-anchor loss. -/
theorem originalTraceRetiredBands_cone_bound {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z)
    (hW : T.RootConeMaximizer H root W W) :
    (T.rootHeadCone root Z).card+T.originalTraceLength tr*(15*k+1)≤
      (T.rootHeadCone root W).card+1 := by
  classical
  obtain ⟨hsub,hcard,_hdis⟩ := T.originalTraceRetiredBands_facts hH hk tr hW
  have hloss := T.originalTraceBandAnchorLoss_le_one hH hk tr
  have hZsub := (T.originalTrace_bounds hH hk tr hW).2.2.1
  have hd : Disjoint (T.originalTraceRetiredBands hH hk tr hW) (T.rootHeadCone root Z) := by
    apply Finset.disjoint_left.mpr
    intro b hb hz
    exact (Finset.mem_sdiff.mp (hsub hb)).2 hz
  have hu : T.originalTraceRetiredBands hH hk tr hW ∪ T.rootHeadCone root Z ⊆
      T.rootHeadCone root W := by
    intro b hb
    rcases Finset.mem_union.mp hb with hb|hb
    · exact (Finset.mem_sdiff.mp (hsub hb)).1
    · exact hZsub hb
  have hc := Finset.card_le_card hu
  rw [Finset.card_union_of_disjoint hd] at hc
  omega

end GreedyShortcuts.ChainDistance.Context
