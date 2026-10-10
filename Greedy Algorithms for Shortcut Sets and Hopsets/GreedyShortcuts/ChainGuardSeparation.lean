import GreedyShortcuts.ChainEntries
import GreedyShortcuts.ChainGuard

/-! A guard inaccessible from an original-path pivot must use new chains.
This is a separation/counting fact, not an injectivity or rectangle theorem. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- A fixed-source path to an inaccessible guard can share only prefix
chains with the original path. Equality of actual earliest entries is what
makes the reachability contradiction possible. -/
theorem guard_shared_chains {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u t z : V} (p : DWalk s u) (q : DWalk u t) (r : DWalk s z)
    (hpq : Allowed (T.graph H s) (p.append q)) (hr : Allowed (T.graph H s) r)
    (hguard : ¬ Reachable T.G u z) :
    T.chainSet r ∩ T.chainSet (p.append q) ⊆ T.chainSet p := by
  classical
  intro c hc
  obtain ⟨hcr,hcpq⟩ := Finset.mem_inter.mp hc
  by_contra hcp
  let e := entry T.chains s c
  have heP : e ∈ (p.append q).support :=
    (T.pathEntries_mem hH (p.append q) hpq (Finset.mem_image.mpr ⟨c,hcpq,rfl⟩)).1
  have heR : e ∈ r.support :=
    (T.pathEntries_mem hH r hr (Finset.mem_image.mpr ⟨c,hcr,rfl⟩)).1
  have hec : label T.chains e = some c := T.entry_label hH r hr hcr
  have henp : e ∉ p.support := fun he => hcp ((T.mem_chainSet p c).mpr ⟨e,he,hec⟩)
  have heq : e ∈ q.support := (Walk.mem_support_append_iff p q).mp heP |>.resolve_left henp
  have hq := ((allowed_append _ p q).mp hpq).2
  have hue : Reachable T.G u e :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨q.takeUntil e heq,allowed_mono (fun _ _ h => h.1)
        (allowed_subwalk hq (q.isSubwalk_takeUntil heq))⟩
  have hez : Reachable T.G e z :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨r.dropUntil e heR,allowed_mono (fun _ _ h => h.1)
        (allowed_subwalk hr (r.isSubwalk_dropUntil heR))⟩
  exact hguard (reachable_trans hue hez)

/-- The actual number of guard-path chains absent from the original path
is at least its distance minus the original prefix count. No multiplicity
of different guards is assumed. -/
theorem guard_offpath_count {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u t z : V} (p : DWalk s u) (q : DWalk u t) (r : DWalk s z)
    (hpq : Allowed (T.graph H s) (p.append q)) (hr : Allowed (T.graph H s) r)
    (hguard : ¬ Reachable T.G u z) :
    T.distance H s z-T.count p ≤ (T.chainSet r \ T.chainSet (p.append q)).card := by
  classical
  have hi := Finset.card_le_card (T.guard_shared_chains hH p q r hpq hr hguard)
  have he := Finset.card_sdiff_add_card_inter (T.chainSet r) (T.chainSet (p.append q))
  have hsz : Reachable T.G s z :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨r,allowed_mono (fun _ _ h => h.1) hr⟩
  have hd := T.distance_le_walk H hsz r hr
  unfold count at hi hd ⊢
  omega

/-- Concrete original-source entries on one path but absent from another. -/
noncomputable def offPathEntries {s z t : V} (r : DWalk s z) (w : DWalk s t) : Finset V :=
  T.pathEntries r \ w.support.toFinset

theorem offPathEntries_spec {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s z t v : V} (r : DWalk s z) (w : DWalk s t)
    (hr : Allowed (T.graph H s) r) (hv : v ∈ T.offPathEntries r w) :
    v ∈ r.support ∧ v ∉ w.support ∧ (s,v) ∈ T.important := by
  classical
  obtain ⟨hvr,hvw⟩ := Finset.mem_sdiff.mp hv
  have h := T.pathEntries_mem hH r hr hvr
  exact ⟨h.1,fun hw => hvw (List.mem_toFinset.mpr hw),h.2⟩

/-- Distinct off-path chains provide distinct actual important entries,
without claiming any rebased distance or shared-minimum-path property. -/
theorem offPathEntries_card {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s z t : V} (r : DWalk s z) (w : DWalk s t)
    (hr : Allowed (T.graph H s) r) :
    (T.chainSet r \ T.chainSet w).card ≤ (T.offPathEntries r w).card := by
  classical
  let C := T.chainSet r \ T.chainSet w
  have hi : (C.image (entry T.chains s)).card=C.card := by
    apply Finset.card_image_iff.mpr
    intro c hc d hd he
    exact Option.some.inj ((T.entry_label hH r hr (Finset.mem_sdiff.mp hc).1).symm.trans
      ((congrArg (label T.chains) he).trans
        (T.entry_label hH r hr (Finset.mem_sdiff.mp hd).1)))
  rw [← hi]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hv
  have hcr := (Finset.mem_sdiff.mp hc).1
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨c,hcr,rfl⟩,?_⟩
  intro hw
  exact (Finset.mem_sdiff.mp hc).2 ((T.mem_chainSet w c).mpr
    ⟨entry T.chains s c,List.mem_toFinset.mp hw,T.entry_label hH r hr hcr⟩)

/-- The same guard supply is witnessed by an actual finite set of distinct
vertices off the original path. -/
theorem guard_offpath_entries {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u t z : V} (p : DWalk s u) (q : DWalk u t) (r : DWalk s z)
    (hpq : Allowed (T.graph H s) (p.append q)) (hr : Allowed (T.graph H s) r)
    (hguard : ¬ Reachable T.G u z) :
    T.distance H s z-T.count p ≤ (T.offPathEntries r (p.append q)).card :=
  (T.guard_offpath_count hH p q r hpq hr hguard).trans
    (T.offPathEntries_card hH r (p.append q) hr)

/-- A genuine strict triangle failure constructs an actual minimum guard
path with the indicated off-path chain supply. Its source is still s. -/
theorem exists_guard_offpath_supply {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u t : V} (p : DWalk s u) (q : DWalk u t)
    (hpq : Allowed (T.graph H s) (p.append q))
    (hcheap : T.count p+T.distance H u t < T.distance H s t) :
    ∃ z, (s,z) ∈ T.important ∧ ¬ Reachable T.G u z ∧
      ∃ r : DWalk s z, Allowed (T.graph H s) r ∧ T.count r=T.distance H s z ∧
        T.distance H s t+1 ≤
          (T.chainSet r \ T.chainSet (p.append q)).card+T.count p+T.distance H u t := by
  have hparts := (allowed_append _ p q).mp hpq
  have hsu : Reachable T.G s u :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨p,allowed_mono (fun _ _ h => h.1) hparts.1⟩
  have hut : Reachable T.G u t :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨q,allowed_mono (fun _ _ h => h.1) hparts.2⟩
  rcases T.distance_guard_dichotomy hH hsu hut with htri | hg
  · have hp := T.distance_le_walk H hsu p hparts.1
    omega
  · obtain ⟨z,hpair,hsz,_hzt,huz,hgap⟩ := hg
    obtain ⟨r,hr,hcount⟩ := T.distance_spec H hsz
    have hsupply := T.guard_offpath_count hH p q r hpq hr huz
    exact ⟨z,hpair,huz,r,hr,hcount,by omega⟩

end GreedyShortcuts.ChainDistance.Context
