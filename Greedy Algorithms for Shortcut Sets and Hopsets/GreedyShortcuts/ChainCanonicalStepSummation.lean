import GreedyShortcuts.ChainFiniteSuffixCard

/-! SOURCE ONLY, UNCOMPILED. Actual per-row remaining-count distribution,
marker-aware summatory lower bound and SAME-step FULL-cap aggregate. A sum
of record bounds has a center-count multiplier, not one alternative gain. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- Actual suffix membership agrees with the injective physical-head
order. Forward uses original route plus DAG antisymmetry; backward uses
the proved original order and the actual dropUntil membership contract. -/
theorem originalCanonicalPhysicalExterior_suffix_order {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U v w : V}
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index))
    (hv : v ∈ T.originalCanonicalPhysicalExterior d y)
    (hw : w ∈ T.originalCanonicalPhysicalExterior d y) :
    let hvQ := List.mem_toFinset.mp (Finset.mem_inter.mp hv).2
    w ∈ ((T.originalOwnerCanonicalTail d y).dropUntil v hvQ).support ↔
      T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y) v≤
        T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y) w := by
  let hvQ := List.mem_toFinset.mp (Finset.mem_inter.mp hv).2
  let r := T.originalOwnerCanonicalTail d y
  let q := r.dropUntil v hvQ
  obtain ⟨_hrootb,hr⟩ := T.originalCanonicalTail_root hH d y
  have hq := allowed_subwalk hr.1 (r.isSubwalk_dropUntil hvQ)
  constructor
  · intro hwq
    have hvw : Reachable T.G v w :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        ⟨q.takeUntil w hwq,allowed_mono (fun _ _ h => h.1)
          (allowed_subwalk hq (q.isSubwalk_takeUntil hwq))⟩
    by_contra hn
    have horder : T.rootTailHeadPosition root r w≤T.rootTailHeadPosition root r v := by
      dsimp only [r]
      omega
    have hwv := T.originalCanonicalPhysicalExterior_order hH d y hw hv horder
    have he : v=w := (GreedyShortcuts.CanonicalSegments.acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ hvw hwv
    exact hn (by simpa only [he] using
      (Nat.le_refl (T.rootTailHeadPosition root r w)))
  · intro horder
    have hvw := T.originalCanonicalPhysicalExterior_order hH d y hv hw horder
    exact T.actual_forward_mem_dropUntil hH r hr.1 hvQ
      (List.mem_toFinset.mp (Finset.mem_inter.mp hw).2) hvw

theorem originalCanonicalRemainingCount_suffixCard {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U v : V}
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index))
    (hv : v ∈ T.originalCanonicalPhysicalExterior d y) :
    T.originalCanonicalRemainingCount d v=
      finiteSuffixCard (T.originalCanonicalPhysicalExterior d y)
        (T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y)) v := by
  classical
  let hvQ := List.mem_toFinset.mp (Finset.mem_inter.mp hv).2
  let q := (T.originalOwnerCanonicalTail d y).dropUntil v hvQ
  have hcard := (T.originalCanonicalPhysicalExterior_remaining hH d y hv).2
  have hset : T.originalCanonicalPhysicalExterior d y ∩ q.support.toFinset=
      (T.originalCanonicalPhysicalExterior d y).filter
        (fun w => T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y) v≤
          T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y) w) := by
    ext w
    constructor
    · intro hw
      obtain ⟨hwC,hwQ⟩ := Finset.mem_inter.mp hw
      exact Finset.mem_filter.mpr ⟨hwC,
        (T.originalCanonicalPhysicalExterior_suffix_order hH d y hv hwC).mp (List.mem_toFinset.mp hwQ)⟩
    · intro hw
      obtain ⟨hwC,hwOrder⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_inter.mpr ⟨hwC,List.mem_toFinset.mpr
        ((T.originalCanonicalPhysicalExterior_suffix_order hH d y hv hwC).mpr hwOrder)⟩
  calc
    T.originalCanonicalRemainingCount d v=
        (T.originalCanonicalPhysicalExterior d y ∩ q.support.toFinset).card := hcard.symm
    _ =finiteSuffixCard (T.originalCanonicalPhysicalExterior d y)
        (T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y)) v :=
      congrArg Finset.card hset

/-- Exact remaining-count distribution for EVERY natural test weight.
It comes from actual suffix sets/order, not positions equated with ranks. -/
theorem originalCanonical_row_distribution {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) (f : ℕ → ℕ) :
    (∑ v ∈ T.originalCanonicalPhysicalExterior d y,f (T.originalCanonicalRemainingCount d v))=
      ∑ j ∈ Finset.range (T.originalCanonicalPhysicalExterior d y).card,f (j+1) := by
  classical
  calc
    _ =∑ v ∈ T.originalCanonicalPhysicalExterior d y,
        f (finiteSuffixCard (T.originalCanonicalPhysicalExterior d y)
          (T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y)) v) :=
      Finset.sum_congr rfl (fun v hv => congrArg f (T.originalCanonicalRemainingCount_suffixCard hH d y hv))
    _ =_ := finiteSuffixCard_sum _ _
      (fun v hv w hw he => T.originalCanonicalPhysicalExterior_order_injective d y hv hw he) f

theorem originalCanonical_row_summatory {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    (∑ v ∈ T.originalCanonicalPhysicalExterior d y,T.originalCanonicalRowWeight d y v)=
      canonicalMidpointSum (T.originalCanonicalPhysicalExterior d y).card := by
  classical
  calc
    _ =∑ v ∈ T.originalCanonicalPhysicalExterior d y,
        canonicalMidpointWeight (T.originalCanonicalRemainingCount d v) :=
      Finset.sum_congr rfl (fun v hv => T.originalCanonicalRowWeight_eq d y
        (List.mem_toFinset.mp (Finset.mem_inter.mp hv).2))
    _ =_ := T.originalCanonical_row_distribution hH d y canonicalMidpointWeight

/-- The marker debit is retained: only S(Delta-1), not S(Delta), follows
from the already proved Delta<=physicalExterior.card+1. W stays in C_y;
its zero term is NOT removed from the row cardinal a second time. -/
theorem originalCanonical_row_marker_lower {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    canonicalMidpointSum (T.distance H root W-T.distance H root U-1)≤
      ∑ v ∈ T.originalCanonicalPhysicalExterior d y,T.originalCanonicalRowWeight d y v := by
  rw [T.originalCanonical_row_summatory hH d y]
  have hd := (T.originalCanonicalPhysicalExterior_drop hH hk hW d y).2.1
  exact canonicalMidpointSum_mono (by omega)

/-- An actual finite row expression, not a field postulating a budget. -/
noncomputable def originalCanonicalStepWeight {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U) : ℕ :=
  ∑ y,canonicalMidpointSum (T.originalCanonicalPhysicalExterior d y).card

theorem originalCanonicalStepWeight_incidence {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (d : T.OriginalSelectorStepData H root k W U) :
    T.originalCanonicalStepWeight d=∑ v ∈ T.originalStepFullCut d,
      (T.originalOwnerCanonicalGroup d v).card*canonicalMidpointWeight (T.originalCanonicalRemainingCount d v) := by
  classical
  calc
    _ =∑ y,∑ v ∈ T.originalCanonicalPhysicalExterior d y,T.originalCanonicalRowWeight d y v :=
      Finset.sum_congr rfl (fun y _hy => (T.originalCanonical_row_summatory hH d y).symm)
    _ =_ := T.originalCanonicalPhysicalExterior_weighted_sum hH d

theorem originalCanonicalStepWeight_cap {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) (M : ℕ)
    (hcap : ∀ e ∈ candidates T.G,T.potential H-T.potential (insert e H)≤M) :
    T.originalCanonicalStepWeight d≤(T.originalStepFullCut d).card*M := by
  classical
  rw [T.originalCanonicalStepWeight_incidence hH d]
  calc
    _ ≤∑ _v ∈ T.originalStepFullCut d,M :=
      Finset.sum_le_sum (fun v hv => T.originalCanonical_center_cap hH hW d hv M hcap)
    _ =_ := by simp

/-- W's zero weight removes ONE center from the multiplier, not another
row head or target. This bounds separate record contributions by M; it
never bounds the sum of alternative edge gains by one M. -/
theorem originalCanonicalStepWeight_cap_without_W {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) (M : ℕ)
    (hcap : ∀ e ∈ candidates T.G,T.potential H-T.potential (insert e H)≤M) :
    T.originalCanonicalStepWeight d≤(T.originalStepFullCut d \ {W}).card*M := by
  classical
  let f := fun v => (T.originalOwnerCanonicalGroup d v).card*
    canonicalMidpointWeight (T.originalCanonicalRemainingCount d v)
  have hsum : (∑ v ∈ T.originalStepFullCut d \ {W},f v)=∑ v ∈ T.originalStepFullCut d,f v := by
    apply Finset.sum_subset Finset.sdiff_subset
    intro v hv hn
    have he : v=W := by
      by_contra hne
      exact hn (Finset.mem_sdiff.mpr ⟨hv,by simpa only [Finset.mem_singleton] using hne⟩)
    subst v
    simp only [f,T.originalCanonicalRemainingCount_W_weight d,Nat.mul_zero]
  rw [T.originalCanonicalStepWeight_incidence hH d,← hsum]
  calc
    _ ≤∑ _v ∈ T.originalStepFullCut d \ {W},M :=
      Finset.sum_le_sum (fun v hv => T.originalCanonical_center_cap hH hW d (Finset.mem_sdiff.mp hv).1 M hcap)
    _ =_ := by simp

/-- Actual step geometry, including zero rank drop and terminal anchor,
still removes W physically. The multiplier's one-center debit is exact. -/
theorem originalCanonical_cut_W_card {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) :
    W ∈ T.originalStepFullCut d ∧
      (T.originalStepFullCut d \ {W}).card+1=(T.originalStepFullCut d).card := by
  classical
  obtain ⟨_hip,hUW,_hU,_hsub,_hp,hcard,_hl,_hu,_hD,_ht,_hr,_hs⟩ :=
    (T.originalSelectorStepData_facts hH hk hW d).1
  have hn : W ∉ T.rootHeadCone root U := by
    intro hWU
    have he : W=U := (GreedyShortcuts.CanonicalSegments.acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _
      (T.mem_rootHeadCone_iff.mp hWU).2.1 hUW
    rw [he] at hcard
    omega
  have hw : W ∈ T.originalStepFullCut d := Finset.mem_sdiff.mpr ⟨hW.1,hn⟩
  have hsub : ({W} : Finset V) ⊆ T.originalStepFullCut d := by
    intro v hv
    simpa only [Finset.mem_singleton.mp hv] using hw
  have hc := Finset.card_sdiff_add_card_inter (T.originalStepFullCut d) {W}
  rw [Finset.inter_eq_right.mpr hsub,Finset.card_singleton] at hc
  exact ⟨hw,hc⟩

theorem originalCanonicalStepWeight_population_lower {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) :
    Fintype.card (T.RootOwner root (d.corridor.getVert d.index))*
      canonicalMidpointSum (T.distance H root W-T.distance H root U-1)≤
        T.originalCanonicalStepWeight d := by
  classical
  calc
    _ =∑ _y : T.RootOwner root (d.corridor.getVert d.index),
        canonicalMidpointSum (T.distance H root W-T.distance H root U-1) := by simp
    _ ≤∑ y,canonicalMidpointSum (T.originalCanonicalPhysicalExterior d y).card := by
      apply Finset.sum_le_sum
      intro y _hy
      have hl := T.originalCanonical_row_marker_lower hH hk hW d y
      rwa [T.originalCanonical_row_summatory hH d y] at hl

/-- Actual SAME-step sandwich with every multiplier/debit retained.
The population is its real finite owner cardinal; no lower population or
temporal payment is supplied. The upper multiplier excludes W once. -/
theorem originalCanonicalStepWeight_sandwich {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) (M : ℕ)
    (hcap : ∀ e ∈ candidates T.G,T.potential H-T.potential (insert e H)≤M) :
    Fintype.card (T.RootOwner root (d.corridor.getVert d.index))*
        canonicalMidpointSum (T.distance H root W-T.distance H root U-1)≤
      T.originalCanonicalStepWeight d ∧
    T.originalCanonicalStepWeight d≤(T.originalStepFullCut d \ {W}).card*M ∧
    (T.originalStepFullCut d \ {W}).card+1=(T.originalStepFullCut d).card := by
  exact ⟨T.originalCanonicalStepWeight_population_lower hH hk hW d,
    T.originalCanonicalStepWeight_cap_without_W hH hW d M hcap,
    (T.originalCanonical_cut_W_card hH hk hW d).2⟩

end GreedyShortcuts.ChainDistance.Context
