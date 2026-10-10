import GreedyShortcuts.ChainGuardSeparation

/-! A fixed-source target cone records original earliest entries that can
reach the target. Guard replacement deletes actual suffix chains from this
finite set; this is additive depletion, not logarithmic volume reduction. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def sourceChains (s : V) : Finset I := by
  classical
  exact Finset.univ.filter (fun c => label T.chains (entry T.chains s c)=some c ∧
    (s,entry T.chains s c) ∈ T.important)

noncomputable def coneChains (s t : V) : Finset I := by
  classical
  exact (T.sourceChains s).filter (fun c => Reachable T.G (entry T.chains s c) t)

theorem coneChains_subset (s t : V) : T.coneChains s t ⊆ T.sourceChains s := by
  classical
  exact Finset.filter_subset _ _

theorem sourceChains_card (s : V) : (T.sourceChains s).card ≤ Fintype.card I :=
  Finset.card_le_univ _

/-- Moving the target backward in original reachability shrinks the same
fixed-source entry cone. Source selectors are never recomputed relative to z. -/
theorem coneChains_mono {s z t : V} (hzt : Reachable T.G z t) :
    T.coneChains s z ⊆ T.coneChains s t := by
  classical
  intro c hc
  obtain ⟨hcs,hcz⟩ := Finset.mem_filter.mp hc
  exact Finset.mem_filter.mpr ⟨hcs,reachable_trans hcz hzt⟩

/-- Every chain on an actual fixed-source path contributes its canonical
entry to the source-to-target cone. -/
theorem chainSet_subset_cone {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (p : DWalk s t) (hp : Allowed (T.graph H s) p) :
    T.chainSet p ⊆ T.coneChains s t := by
  classical
  intro c hc
  have he := T.pathEntries_mem hH p hp (Finset.mem_image.mpr ⟨c,hc,rfl⟩)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,T.entry_label hH p hp hc,he.2⟩,?_⟩
  exact (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
    ⟨p.dropUntil (entry T.chains s c) he.1,allowed_mono (fun _ _ h => h.1)
      (allowed_subwalk hp (p.isSubwalk_dropUntil he.1))⟩

/-- Every chain occurring only after the pivot is removed from the guard
cone. This deletion can be charged only once along a shrinking cone sequence. -/
theorem guard_cone_disjoint {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u t z : V} (p : DWalk s u) (q : DWalk u t)
    (hpq : Allowed (T.graph H s) (p.append q)) (hguard : ¬ Reachable T.G u z) :
    Disjoint (T.chainSet (p.append q) \ T.chainSet p) (T.coneChains s z) := by
  classical
  apply Finset.disjoint_left.mpr
  intro c hc hcz
  obtain ⟨hcpq,hcnp⟩ := Finset.mem_sdiff.mp hc
  have he := (T.pathEntries_mem hH (p.append q) hpq (Finset.mem_image.mpr ⟨c,hcpq,rfl⟩)).1
  have hlabel := T.entry_label hH (p.append q) hpq hcpq
  have henp : entry T.chains s c ∉ p.support :=
    fun hv => hcnp ((T.mem_chainSet p c).mpr ⟨_,hv,hlabel⟩)
  have heq := (Walk.mem_support_append_iff p q).mp he |>.resolve_left henp
  have hue : Reachable T.G u (entry T.chains s c) :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨q.takeUntil _ heq,allowed_mono (fun _ _ h => h.1)
        (allowed_subwalk ((allowed_append _ p q).mp hpq).2 (q.isSubwalk_takeUntil heq))⟩
  exact hguard (reachable_trans hue (Finset.mem_filter.mp hcz).2)

/-- Exact additive cone depletion by all the original path's nonprefix
chains. No distinct-guard or multiplicative-depletion assumption occurs. -/
theorem guard_cone_depletion {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u t z : V} (p : DWalk s u) (q : DWalk u t)
    (hpq : Allowed (T.graph H s) (p.append q))
    (hguard : ¬ Reachable T.G u z) (hzt : Reachable T.G z t) :
    (T.coneChains s z).card+T.count (p.append q) ≤
      (T.coneChains s t).card+T.count p := by
  classical
  have hc := T.chainSet_subset_cone hH (p.append q) hpq
  have hu : (T.chainSet (p.append q) \ T.chainSet p) ∪ T.coneChains s z ⊆
      T.coneChains s t :=
    Finset.union_subset (fun _ hx => hc (Finset.mem_sdiff.mp hx).1) (T.coneChains_mono hzt)
  have hcard := Finset.card_le_card hu
  rw [Finset.card_union_of_disjoint (T.guard_cone_disjoint hH p q hpq hguard)] at hcard
  have hp : T.chainSet p ⊆ T.chainSet (p.append q) := by
    rw [T.chainSet_append]
    exact Finset.subset_union_left
  have he := Finset.card_sdiff_add_card_inter (T.chainSet (p.append q)) (T.chainSet p)
  rw [Finset.inter_eq_right.mpr hp] at he
  unfold count
  omega

end GreedyShortcuts.ChainDistance.Context
