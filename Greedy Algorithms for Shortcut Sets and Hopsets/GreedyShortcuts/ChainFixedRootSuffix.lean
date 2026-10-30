import GreedyShortcuts.ChainOwnerLastRootTail

/-! SOURCE ONLY, UNCOMPILED. All suffix minimization keeps ONE fixed ROOT
filter. Literal LAST tails are minimal in that filter and may be replaced
by its shared per-entry choices without changing the original owner price.
Coalescence of independently chosen ties at later vertices is NOT asserted. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- ROOT admission transfers to the actual owner's unchanged filter only
with BOTH original reachability links. The tail starts at b, not at x;
this is not the generally false converse to allowed_rebase. -/
theorem fixed_root_tail_owner_admission {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root x b W : V}
    (hrootx : Reachable T.G root x) (hxb : Reachable T.G x b)
    (q : DWalk b W) (hq : Allowed (T.graph H root) q) :
    Allowed (T.graph H x) q := by
  classical
  have ha : Allowed (augment T.G (T.base ∪ H)) q :=
    allowed_mono (fun _ _ h => h.1) hq
  intro d hd
  have hh := hq d hd
  refine ⟨hh.1,?_⟩
  rcases hh.2 with hc | hc | hf
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · by_cases hc : label T.chains d.snd=none
    · exact Or.inr (Or.inl hc)
    · apply Or.inr ∘ Or.inr
      apply T.first_inherits hrootx ?_ hc hf
      have hm := q.dart_snd_mem_support_of_mem_darts hd
      have hbd : Reachable T.G b d.snd :=
        (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
          ⟨q.takeUntil d.snd hm,allowed_subwalk ha (q.isSubwalk_takeUntil hm)⟩
      exact reachable_trans hxb hbd

/-- This minimum keeps the SOURCE PARAMETER root even though the native
walk starts at b. It is deliberately not T.distance H b W. -/
def FixedRootSuffixMinimum (H : Finset (V × V)) (root : V)
    {b W : V} (q : DWalk b W) : Prop :=
  Allowed (T.graph H root) q ∧
    ∀ r : DWalk b W,Allowed (T.graph H root) r → T.count q≤T.count r

/-- Existence only on the genuine ROOT-filtered route domain. Original
b-to-W reachability alone is not substituted for this premise. -/
theorem exists_fixedRootSuffixMinimum (H : Finset (V × V)) {root b W : V}
    (hr : Reachable (T.graph H root) b W) :
    ∃ q : DWalk b W,T.FixedRootSuffixMinimum H root q := by
  classical
  have hex : ∃ n : ℕ,∃ q : DWalk b W,
      Allowed (T.graph H root) q ∧ T.count q=n := by
    obtain ⟨q,hq⟩ := hr
    exact ⟨T.count q,q,hq,rfl⟩
  obtain ⟨q,hq,hcount⟩ := Nat.find_spec hex
  refine ⟨q,hq,?_⟩
  intro r hr
  have hle := Nat.find_min' hex ⟨r,hr,rfl⟩
  omega

/-- One shared choice for each literal physical entry in the actual
ROOT-filtered domain. It is independent of owner, row and guard names. -/
noncomputable def fixedRootSuffix (H : Finset (V × V)) (root b W : V)
    (hr : Reachable (T.graph H root) b W) : DWalk b W :=
  Classical.choose (T.exists_fixedRootSuffixMinimum H hr)

theorem fixedRootSuffix_spec (H : Finset (V × V)) (root b W : V)
    (hr : Reachable (T.graph H root) b W) :
    T.FixedRootSuffixMinimum H root (T.fixedRootSuffix H root b W hr) :=
  Classical.choose_spec (T.exists_fixedRootSuffixMinimum H hr)

/-- The route-existence proof cannot retie the per-entry choice. In
particular repeated owner rows with the same physical b use one walk. -/
theorem fixedRootSuffix_proof_irrel (H : Finset (V × V)) (root b W : V)
    (h₁ h₂ : Reachable (T.graph H root) b W) :
    T.fixedRootSuffix H root b W h₁=T.fixedRootSuffix H root b W h₂ := by
  rfl

/-- Every literal LAST tail of the unchanged own-x minimum is genuinely
transition-minimal in the FIXED ROOT filter. The competitor is explicitly
transported to x using x's real prefix, then joined at covered b once. -/
theorem ownerLastRootTail_fixed_root_minimum {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root x W : V}
    (hx : (root,x) ∈ T.important) {Q : DWalk x W}
    (F : T.OwnerLastRootTail H root x W Q)
    (hmin : T.count Q=T.distance H x W) :
    T.FixedRootSuffixMinimum H root F.tail := by
  refine ⟨F.rootTail,?_⟩
  intro r hr
  have hxb : Reachable T.G x F.entry :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨F.prefix,allowed_mono (fun _ _ h => h.1) F.ownPrefix⟩
  have hrx := T.fixed_root_tail_owner_admission hH (T.important_spec hx).1 hxb r hr
  have hnew := (allowed_append _ _ _).mpr ⟨F.ownPrefix,hrx⟩
  have hold := (allowed_append _ _ _).mpr ⟨F.ownPrefix,F.ownTail⟩
  have hxW : Reachable T.G x W :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨F.prefix.append F.tail,allowed_mono (fun _ _ h => h.1) hold⟩
  have hd := T.distance_le_walk H hxW (F.prefix.append r) hnew
  have hcold := T.count_append_exact hH F.prefix F.tail hold
  have hcnew := T.count_append_exact hH F.prefix r hnew
  have hwhole : T.count (F.prefix.append F.tail)=T.distance H x W := by
    rw [← F.split]
    exact hmin
  omega

/-- ANY fixed-ROOT minimum at the actual entry has the original tail's
price. Its explicit splice is own-x admitted and remains an own-x minimum.
The original selected Q is retained as an argument, not silently retied.
ROOT-validity is unchanged, so an old LAST rejected dart remains last. -/
theorem ownerLastRootTail_replace_fixed_root {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root x W : V}
    (hx : (root,x) ∈ T.important) {Q : DWalk x W}
    (F : T.OwnerLastRootTail H root x W Q)
    (hmin : T.count Q=T.distance H x W)
    (r : DWalk F.entry W) (hr : T.FixedRootSuffixMinimum H root r) :
    Allowed (T.graph H x) r ∧
      Allowed (T.graph H x) (F.prefix.append r) ∧
      T.count r=T.count F.tail ∧
      T.count (F.prefix.append r)=T.distance H x W ∧
      F.tau+1=T.count r ∧
      (Allowed (T.graph H root) (F.prefix.append r) ↔
        Allowed (T.graph H root) Q) := by
  have hxb : Reachable T.G x F.entry :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨F.prefix,allowed_mono (fun _ _ h => h.1) F.ownPrefix⟩
  have hrx := T.fixed_root_tail_owner_admission hH (T.important_spec hx).1 hxb r hr.1
  have hnew := (allowed_append _ _ _).mpr ⟨F.ownPrefix,hrx⟩
  have hold := (allowed_append _ _ _).mpr ⟨F.ownPrefix,F.ownTail⟩
  have htailmin := T.ownerLastRootTail_fixed_root_minimum hH hx F hmin
  have heq : T.count r=T.count F.tail :=
    le_antisymm (hr.2 F.tail F.rootTail) (htailmin.2 r hr.1)
  have hcold := T.count_append_exact hH F.prefix F.tail hold
  have hcnew := T.count_append_exact hH F.prefix r hnew
  have hwhole : T.count (F.prefix.append F.tail)=T.distance H x W := by
    rw [← F.split]
    exact hmin
  have hprice : T.count (F.prefix.append r)=T.distance H x W := by omega
  obtain ⟨htau,_hprefix,_hcost⟩ := T.ownerLastRootTail_prices hH F hmin
  have hvalid : Allowed (T.graph H root) (F.prefix.append r) ↔
      Allowed (T.graph H root) Q := by
    constructor
    · intro hnewRoot
      have hp := (allowed_append _ _ _).mp hnewRoot |>.1
      rw [F.split]
      exact (allowed_append _ _ _).mpr ⟨hp,F.rootTail⟩
    · intro hQRoot
      have hQRoot' : Allowed (T.graph H root) (F.prefix.append F.tail) := by
        rw [← F.split]
        exact hQRoot
      have hp := (allowed_append _ _ _).mp hQRoot' |>.1
      exact (allowed_append _ _ _).mpr ⟨hp,hr.1⟩
  exact ⟨hrx,hnew,heq,hprice,by omega,hvalid⟩

/-- The canonical-per-ENTRY choice is available for each actual LAST tail
because THAT tail witnesses its genuine ROOT-filtered reachability. No
choice is made for an inaccessible endpoint. The same unchanged prefix and
all exact original prices are retained; zero-tail/nil cases need no split. -/
theorem ownerLastRootTail_shared_entry_choice {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root x W : V}
    (hx : (root,x) ∈ T.important) {Q : DWalk x W}
    (F : T.OwnerLastRootTail H root x W Q)
    (hmin : T.count Q=T.distance H x W) :
    let r := T.fixedRootSuffix H root F.entry W ⟨F.tail,F.rootTail⟩
    Allowed (T.graph H x) r ∧
      Allowed (T.graph H x) (F.prefix.append r) ∧
      T.count r=T.count F.tail ∧
      T.count (F.prefix.append r)=T.distance H x W ∧
      F.tau+1=T.count r ∧
      (Allowed (T.graph H root) (F.prefix.append r) ↔
        Allowed (T.graph H root) Q) := by
  exact T.ownerLastRootTail_replace_fixed_root hH hx F hmin _
    (T.fixedRootSuffix_spec H root F.entry W ⟨F.tail,F.rootTail⟩)

/-- Suffix optimality is valid when the filter parameter stays ROOT. The
join vertex may be uncovered: the SAME marker cancels on both comparisons.
This does NOT assert equality with an independently chosen tied suffix. -/
theorem fixedRootSuffixMinimum_suffix {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root b v W : V}
    (hrootb : Reachable T.G root b)
    (p : DWalk b v) (q : DWalk v W)
    (hmin : T.FixedRootSuffixMinimum H root (p.append q)) :
    T.FixedRootSuffixMinimum H root q := by
  have hparts := (allowed_append _ _ _).mp hmin.1
  refine ⟨hparts.2,?_⟩
  intro r hr
  have hnew : Allowed (T.graph H root) (p.append r) :=
    (allowed_append _ _ _).mpr ⟨hparts.1,hr⟩
  have holdb := T.allowed_rebase hH hrootb (p.append q) hmin.1
  have hnewb := T.allowed_rebase hH hrootb (p.append r) hnew
  have hcold := T.count_append_exact hH p q holdb
  have hcnew := T.count_append_exact hH p r hnewb
  have hle := hmin.2 (p.append r) hnew
  omega

end GreedyShortcuts.ChainDistance.Context
