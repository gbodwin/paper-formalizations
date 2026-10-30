import GreedyShortcuts.ChainMaximumChildSelector

/-! SOURCE ONLY, UNCOMPILED. Fixed own-owner minima and their LITERAL last
ROOT-good suffixes. No selected walk is retied or replaced. The finite
minimum below ranges over these constructed suffixes, not supplied tails.
No suffix is asserted minimum after changing its original source. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- The actual fixed owner domain. There is no new cone or ROOT field. -/
abbrev RootOwner (root a : V) := {x : V // x ∈ T.rootHeadCone root a}

/-- A family of attained minima in EACH owner's unchanged original filter.
This contains only the native path and its admission/minimum certificate. -/
def OwnerMinimumFamily (H : Finset (V × V)) (root a W : V) :=
  ∀ x : T.RootOwner root a,
    {Q : DWalk x.val W // Allowed (T.graph H x.val) Q ∧
      T.count Q=T.distance H x.val W}

theorem exists_ownerMinimumFamily (H : Finset (V × V)) {root a W : V}
    (haW : Reachable T.G a W) : Nonempty (T.OwnerMinimumFamily H root a W) := by
  classical
  have hex : ∀ x : T.RootOwner root a,
      ∃ Q : DWalk x.val W,Allowed (T.graph H x.val) Q ∧
        T.count Q=T.distance H x.val W := by
    intro x
    exact T.distance_spec H
      (reachable_trans (T.mem_rootHeadCone_iff.mp x.property).2.1 haW)
  exact ⟨fun x => ⟨Classical.choose (hex x),Classical.choose_spec (hex x)⟩⟩

private theorem ownerTail_last_split {A B : V → V → Prop} {x W : V}
    (Q : DWalk x W) (hQ : Allowed A Q) (hbad : ¬ Allowed B Q) :
    ∃ (a b : V) (h : (⊤ : SimpleGraph V).Adj a b)
      (l : DWalk x a) (r : DWalk b W),
      Q=l.append (.cons h r) ∧ Allowed A l ∧ A a b ∧ ¬ B a b ∧
      Allowed A r ∧ Allowed B r := by
  classical
  induction Q with
  | nil => exact (hbad (allowed_nil _ _)).elim
  | @cons x y W h Q ih =>
    obtain ⟨hxy,hQA⟩ := (allowed_cons _ h Q).mp hQ
    by_cases hQB : Allowed B Q
    · have hn : ¬ B x y := by
        intro hb
        exact hbad ((allowed_cons _ h Q).mpr ⟨hb,hQB⟩)
      exact ⟨x,y,h,.nil,Q,rfl,allowed_nil _ _,hxy,hn,hQA,hQB⟩
    · obtain ⟨a,b,h',l,r,he,hl,hab,hnb,hrA,hrB⟩ := ih hQA hQB
      refine ⟨a,b,h',.cons h l,r,?_,
        (allowed_cons _ h l).mpr ⟨hxy,hl⟩,hab,hnb,hrA,hrB⟩
      simp only [he,Walk.cons_append]

/-- Path data for the unchanged Q. In the valid case the whole Q is kept;
otherwise the displayed dart is literally the LAST rejected ROOT entry,
because its ENTIRE following suffix is ROOT-admitted. These are path
certificates, not rank/owner/forcing conclusions packaged as fields. -/
structure OwnerLastRootTail (H : Finset (V × V)) (root x W : V)
    (Q : DWalk x W) where
  entry : V
  «prefix» : DWalk x entry
  tail : DWalk entry W
  split : Q=«prefix».append tail
  ownPrefix : Allowed (T.graph H x) «prefix»
  ownTail : Allowed (T.graph H x) tail
  rootTail : Allowed (T.graph H root) tail
  covered : label T.chains entry≠none
  boundary :
    (Allowed (T.graph H root) Q ∧ entry=x ∧ T.count «prefix»=1) ∨
    ∃ (a : V) (h : (⊤ : SimpleGraph V).Adj a entry) (l : DWalk x a),
      «prefix»=l.append (.cons h .nil) ∧ Allowed (T.graph H x) l ∧
      T.graph H x a entry ∧ ¬ T.graph H root a entry

noncomputable def OwnerLastRootTail.tau {H : Finset (V × V)} {root x W : V}
    {Q : DWalk x W} (F : T.OwnerLastRootTail H root x W Q) : ℕ :=
  T.count F.tail-1

/-- Existence uses precisely the supplied walk. No favorable minimum or
suffix is chosen in place of Q, and the valid branch includes nil walks. -/
theorem exists_ownerLastRootTail {H : Finset (V × V)} {root x W : V}
    (hx : (root,x) ∈ T.important) (Q : DWalk x W)
    (hQ : Allowed (T.graph H x) Q) :
    Nonempty (T.OwnerLastRootTail H root x W Q) := by
  classical
  obtain ⟨c,hxc⟩ := T.important_covered hx
  by_cases hroot : Allowed (T.graph H root) Q
  · have hn : T.count (.nil : DWalk x x)=1 := by
      simp [count,chainSet,hxc]
    exact ⟨⟨x,.nil,Q,by simp,allowed_nil _ _,hQ,hroot,
      by simp [hxc],Or.inl ⟨hroot,rfl,hn⟩⟩⟩
  · obtain ⟨a,b,h,l,r,he,hl,hab,hnb,hr,hrs⟩ := ownerTail_last_split Q hQ hroot
    have hc : label T.chains b≠none := by
      intro hh
      exact hnb ⟨hab.1,Or.inr (Or.inl hh)⟩
    let p : DWalk x b := l.append (.cons h .nil)
    have hp : Allowed (T.graph H x) p :=
      (allowed_append _ _ _).mpr
        ⟨hl,(allowed_cons _ h .nil).mpr ⟨hab,allowed_nil _ _⟩⟩
    have he' : Q=p.append r := by
      simpa only [p,← Walk.append_assoc,Walk.cons_append,Walk.nil_append] using he
    exact ⟨⟨b,p,r,he',hp,hr,hrs,hc,Or.inr ⟨a,h,l,rfl,hl,hab,hnb⟩⟩⟩

/-- Both the marker and prefix price are exact in the ORIGINAL x filter.
tau=0 and a last rejected entry equal to W remain permitted. -/
theorem ownerLastRootTail_prices {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root x W : V} {Q : DWalk x W}
    (F : T.OwnerLastRootTail H root x W Q)
    (hmin : T.count Q=T.distance H x W) :
    F.tau+1=T.count F.tail ∧
      T.count F.prefix=T.distance H x F.entry ∧
      T.distance H x W=T.distance H x F.entry+F.tau := by
  classical
  obtain ⟨c,hbc⟩ := Option.ne_none_iff_exists'.mp F.covered
  have hb : c ∈ T.chainSet F.tail :=
    (T.mem_chainSet F.tail c).mpr ⟨F.entry,F.tail.start_mem_support,hbc⟩
  have hpos : 1 ≤ T.count F.tail := Finset.one_le_card.mpr ⟨c,hb⟩
  have htau : F.tau+1=T.count F.tail := by
    dsimp only [OwnerLastRootTail.tau]
    omega
  have hall := (allowed_append _ _ _).mpr ⟨F.ownPrefix,F.ownTail⟩
  have hwhole : T.count (F.prefix.append F.tail)=T.distance H x W := by
    rw [← F.split]
    exact hmin
  have hp := T.minimum_prefix hH F.prefix F.tail hall hwhole
  have hc := T.count_append_exact hH F.prefix F.tail hall
  have hmarker : (label T.chains F.entry).toFinset.card=1 := by simp [hbc]
  exact ⟨htau,hp,by omega⟩

/-- A ROOT-valid selected row has the actual ROOT rank comparison with
its OWN suffix length. There is no substitution of ROOT rank for d_x(W). -/
theorem ownerLastRootTail_valid_rank {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root x W : V}
    (hx : (root,x) ∈ T.important) {Q : DWalk x W}
    (F : T.OwnerLastRootTail H root x W Q)
    (hmin : T.count Q=T.distance H x W)
    (hvalid : Allowed (T.graph H root) Q) :
    T.distance H root W ≤ T.distance H root x+F.tau := by
  have hpone : T.count F.prefix=1 := by
    rcases F.boundary with hv | ⟨a,h,l,he,_hl,_hab,hnb⟩
    · exact hv.2.2
    · have hv : Allowed (T.graph H root) (F.prefix.append F.tail) := by
        rw [← F.split]
        exact hvalid
      have hprefix := (allowed_append _ _ _).mp hv |>.1
      rw [he] at hprefix
      have hdart := (allowed_append _ _ _).mp hprefix |>.2
      exact (hnb ((allowed_cons _ h .nil).mp hdart).1).elim
  obtain ⟨p,hp,hpc⟩ := T.distance_spec H (T.important_spec hx).1
  obtain ⟨c,hxc⟩ := T.important_covered hx
  have hrootW : Reachable T.G root W :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨p.append Q,allowed_mono (fun _ _ h => h.1)
        ((allowed_append _ _ _).mpr ⟨hp,hvalid⟩)⟩
  have hd := T.distance_le_walk H hrootW (p.append Q)
    ((allowed_append _ _ _).mpr ⟨hp,hvalid⟩)
  have hc := T.count_append_covered p Q hxc
  obtain ⟨_htau,hprefix,hprice⟩ := T.ownerLastRootTail_prices hH F hmin
  omega

/-- Native LAST guard, now priced by the ACTUAL good tail rather than the
whole row. The ROOT-important guard lies in its own ROOT cone. No removal,
band location, or containment of other projected heads is asserted.
No old-owner suffix optimality or changed-source minimum is used. -/
theorem ownerLastRootTail_invalid_guard {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root x W : V}
    (hx : (root,x) ∈ T.important) {Q : DWalk x W}
    (F : T.OwnerLastRootTail H root x W Q)
    (hbad : ¬ Allowed (T.graph H root) Q) :
    ∃ g,(root,g) ∈ T.important ∧ g=first T.chains root F.entry ∧
      Reachable T.G g W ∧ ¬ Reachable T.G x g ∧
      T.distance H root W ≤ T.distance H root g+F.tau := by
  classical
  rcases F.boundary with hv | ⟨a,h,l,he,hl,hab,hnb⟩
  · exact (hbad hv.1).elim
  have hdiff : label T.chains a≠label T.chains F.entry := by
    intro hh
    exact hnb ⟨hab.1,Or.inl hh⟩
  have hfirst : first T.chains x F.entry=F.entry :=
    hab.2.resolve_left hdiff |>.resolve_left F.covered
  have hnfirst : first T.chains root F.entry≠F.entry := by
    intro hh
    exact hnb ⟨hab.1,Or.inr (Or.inr hh)⟩
  obtain ⟨c,hbc⟩ := Option.ne_none_iff_exists'.mp F.covered
  have hxb : Reachable T.G x F.entry :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨F.prefix,allowed_mono (fun _ _ h => h.1) F.ownPrefix⟩
  have hrootb := reachable_trans (T.important_spec hx).1 hxb
  have hf := first_spec T.chains T.disjoint root F.entry hrootb F.covered
  let g := first T.chains root F.entry
  have hgc : label T.chains g=some c := hf.2.2.trans hbc
  have hbW : Reachable T.G F.entry W :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨F.tail,allowed_mono (fun _ _ h => h.1) F.rootTail⟩
  have hxg : ¬ Reachable T.G x g := by
    intro hh
    have hxf := first_spec T.chains T.disjoint x g hh (by simp [hgc])
    have hsame : first T.chains x g=F.entry :=
      (first_constant T.chains x g F.entry hf.2.2).trans hfirst
    rw [hsame] at hxf
    have heq : g=F.entry :=
      (acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ hf.2.1 hxf.2.1
    exact hnfirst heq
  obtain ⟨p,hp,hpc⟩ := T.distance_spec H hf.1
  obtain ⟨internal,hi,_hlen,hicolor⟩ := ChainCover.internal_short T hH hf.2.1 hgc hbc
  have hir : Allowed (T.graph H root) internal := T.allowed_internal internal hi hicolor
  have hall := (allowed_append _ _ _).mpr
    ⟨(allowed_append _ _ _).mpr ⟨hp,hir⟩,F.rootTail⟩
  have hd := T.distance_le_walk H (reachable_trans hf.1 (reachable_trans hf.2.1 hbW))
    ((p.append internal).append F.tail) hall
  have hc := T.count_append_covered (p.append internal) F.tail hbc
  rw [T.count_append_internal p internal hicolor,hpc] at hc
  have hbmem : c ∈ T.chainSet F.tail :=
    (T.mem_chainSet F.tail c).mpr ⟨F.entry,F.tail.start_mem_support,hbc⟩
  have hpos : 1 ≤ T.count F.tail := Finset.one_le_card.mpr ⟨c,hbmem⟩
  have htau : F.tau+1=T.count F.tail := by
    dsimp only [OwnerLastRootTail.tau]
    omega
  exact ⟨g,T.first_important hrootb hbc,rfl,reachable_trans hf.2.1 hbW,hxg,by dsimp only [g] at *; omega⟩

/-- Construct the literal-LAST tail family of ANY already fixed family of
own-owner minima. Choice only extracts an actual split of each unchanged Q.
The whole shared canonical ROOT suffix system is a separate pending seam. -/
theorem exists_ownerLastRootTailFamily {H : Finset (V × V)} {root a W : V}
    (Q : T.OwnerMinimumFamily H root a W) :
    Nonempty (∀ x : T.RootOwner root a,
      T.OwnerLastRootTail H root x.val W (Q x).val) := by
  classical
  exact ⟨fun x => Classical.choice (T.exists_ownerLastRootTail
    (T.mem_rootHeadCone_iff.mp x.property).1 (Q x).val (Q x).property.1)⟩

/-- The finite comparison has a REAL attaining owner in the original cone.
This does not select its minimum walk again or presuppose a useful floor. -/
theorem exists_minimum_owner_tail {H : Finset (V × V)} {root a W : V}
    (ha : (root,a) ∈ T.important) (Q : T.OwnerMinimumFamily H root a W)
    (F : ∀ x : T.RootOwner root a,
      T.OwnerLastRootTail H root x.val W (Q x).val) :
    ∃ x : T.RootOwner root a,∀ y : T.RootOwner root a,(F x).tau≤(F y).tau := by
  classical
  let owner : T.RootOwner root a := ⟨a,T.rootCone_self_mem ha⟩
  obtain ⟨x,_hx,hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (T.RootOwner root a))
    (fun y => (F y).tau) ⟨owner,Finset.mem_univ owner⟩
  exact ⟨x,fun y => hmin y (Finset.mem_univ y)⟩

/-- The REAL minimum-tail comparison excludes ROOT validity of its actual
attaining row on the strict guard side. x is not an arbitrary invalid row:
it is the supplied attaining owner of the fixed family. This is the native
input to the original guard mode, with no assumed canonical suffix price. -/
theorem minimum_owner_tail_strict_guard {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root a W Vmax : V}
    (Q : T.OwnerMinimumFamily H root a W)
    (F : ∀ x : T.RootOwner root a,
      T.OwnerLastRootTail H root x.val W (Q x).val)
    (x : T.RootOwner root a)
    (hminTail : ∀ y : T.RootOwner root a,(F x).tau≤(F y).tau)
    (hmax : T.RootConeMaximizer H root a Vmax)
    (hstrict : T.distance H root Vmax+(F x).tau<T.distance H root W) :
    (∀ y : T.RootOwner root a,(F x).tau≤(F y).tau) ∧
      ¬ Allowed (T.graph H root) (Q x).val ∧
      ∃ g,(root,g) ∈ T.important ∧ g=first T.chains root (F x).entry ∧
        Reachable T.G g W ∧ ¬ Reachable T.G x.val g ∧
        T.distance H root W≤T.distance H root g+(F x).tau ∧
        T.distance H root Vmax<T.distance H root g := by
  have hx := (T.mem_rootHeadCone_iff.mp x.property).1
  have hbad : ¬ Allowed (T.graph H root) (Q x).val := by
    intro hv
    have hrank := T.ownerLastRootTail_valid_rank hH hx (F x) (Q x).property.2 hv
    have hbound := hmax.2 x.val x.property
    omega
  obtain ⟨g,hg,he,hgW,hxg,hprice⟩ := T.ownerLastRootTail_invalid_guard hH hx (F x) hbad
  exact ⟨hminTail,hbad,g,hg,he,hgW,hxg,hprice,by omega⟩

end GreedyShortcuts.ChainDistance.Context
