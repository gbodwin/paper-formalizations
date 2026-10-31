import GreedyShortcuts.ChainCanonicalOwnerCut
import GreedyShortcuts.ChainEntryLevels

/-! Actual noninitial chain levels of the SAME
fixed-ROOT suffix. Physical indices witness attained levels; they are not
identified with chain ranks. No minimum is moved to the suffix source. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- Prefix optimality with the ORIGINAL fixed filter parameter. Admission
is rebased only to invoke exact chain counting, never to inherit a minimum. -/
theorem fixedRootSuffixMinimum_prefix {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root b w W : V}
    (hrootb : Reachable T.G root b) (p : DWalk b w) (s : DWalk w W)
    (hmin : T.FixedRootSuffixMinimum H root (p.append s)) :
    T.FixedRootSuffixMinimum H root p := by
  have hp := (allowed_append _ _ _).mp hmin.1
  refine ⟨hp.1,?_⟩
  intro r hr
  have hnew := (allowed_append _ _ _).mpr ⟨hr,hp.2⟩
  have holdb := T.allowed_rebase hH hrootb (p.append s) hmin.1
  have hnewb := T.allowed_rebase hH hrootb (r.append s) hnew
  have hcold := T.count_append_exact hH p s holdb
  have hcnew := T.count_append_exact hH r s hnewb
  have hle := hmin.2 (r.append s) hnew
  omega

/-- First attainment in the fixed ROOT filter produces a physical
ROOT-first entry, even though the native walk starts later at b. -/
theorem rootSuffix_prefix_level_important {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root b W : V}
    (hrootb : Reachable T.G root b) (q : DWalk b W)
    (hq : Allowed (T.graph H root) q) (i : ℕ) (hi : i<q.length)
    (hinc : T.count (q.take i)<T.count (q.take (i+1))) :
    (root,q.getVert (i+1)) ∈ T.important := by
  classical
  have hset := T.chainSet_take_succ q i
  have hlabel : label T.chains (q.getVert (i+1))≠none := by
    intro hn
    simp only [hn,Option.toFinset_none,Finset.union_empty] at hset
    have he : T.count (q.take (i+1))=T.count (q.take i) := congrArg Finset.card hset
    omega
  obtain ⟨c,hc⟩ := Option.ne_none_iff_exists'.mp hlabel
  have hcnot : c ∉ T.chainSet (q.take i) := by
    intro hm
    simp only [hc,Option.toFinset_some,Finset.union_singleton,Finset.insert_eq_of_mem hm] at hset
    have he : T.count (q.take (i+1))=T.count (q.take i) := congrArg Finset.card hset
    omega
  have hprev : label T.chains (q.getVert i)≠label T.chains (q.getVert (i+1)) := by
    intro he
    exact hcnot ((T.mem_chainSet (q.take i) c).mpr
      ⟨q.getVert i,(q.take i).end_mem_support,he.trans hc⟩)
  have hedge := allowed_vertex_step q hq i hi
  have hf := hedge.2.resolve_left hprev |>.resolve_left hlabel
  have hbi : Reachable T.G b (q.getVert (i+1)) :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨q.take (i+1),allowed_mono (fun _ _ h => h.1)
        (allowed_subwalk hq (q.isSubwalk_take (i+1)))⟩
  simpa only [hf] using T.first_important (reachable_trans hrootb hbi) hc

theorem rootSuffix_exists_important_prefix_count {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root b W : V}
    (hrootb : Reachable T.G root b) (q : DWalk b W)
    (hq : Allowed (T.graph H root) q) (ell : ℕ)
    (hell : 2≤ell) (hellq : ell≤T.count q) :
    ∃ i,i≤q.length ∧ T.count (q.take i)=ell ∧ (root,q.getVert i) ∈ T.important := by
  obtain ⟨i,hi,hil,hcount,hprev⟩ := T.exists_prefix_count q ell hell hellq
  have he : i-1+1=i := Nat.sub_add_cancel (by omega)
  have hip := T.rootSuffix_prefix_level_important hH hrootb q hq (i-1)
    (by omega) (by rw [he];omega)
  exact ⟨i,hil,hcount,by simpa only [he] using hip⟩

/-- If the start is itself ROOT-first, ALL projected heads are literal
vertices. The nonglobal initial-marker exception has been discharged. -/
theorem rootTailHeads_physical {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root b W : V} (q : DWalk b W)
    (hq : Allowed (T.graph H root) q) (hb : (root,b) ∈ T.important) :
    T.rootTailHeads root q ⊆ q.support.toFinset := by
  intro t ht
  by_cases he : t=b
  · simpa only [he] using List.mem_toFinset.mpr q.start_mem_support
  · have hn : t≠first T.chains root b := by simpa only [(T.important_spec hb).2] using he
    exact List.mem_toFinset.mpr
      (T.rootTailHead_nonmarker_physical hH (T.important_spec hb).1 q hq ht hn).2

theorem rootTailHeads_of_important_mem {root b W t : V} (q : DWalk b W)
    (hip : (root,t) ∈ T.important) (ht : t ∈ q.support) :
    t ∈ T.rootTailHeads root q := by
  classical
  obtain ⟨c,hc⟩ := T.important_covered hip
  have he : entry T.chains root c=t := by simpa only [first,hc] using (T.important_spec hip).2
  exact Finset.mem_image.mpr ⟨c,(T.mem_chainSet q c).mpr ⟨t,ht,hc⟩,he⟩

/-- The actual suffix targets are precisely its ROOT chain heads, not
physical slots or all later vertices. This equality keeps W exactly once. -/
theorem rootTailHeads_suffix_targets {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root b w W : V}
    (hrootb : Reachable T.G root b) (p : DWalk b w) (s : DWalk w W)
    (hq : Allowed (T.graph H root) (p.append s)) (hw : (root,w) ∈ T.important) :
    T.rootTailHeads root (p.append s) ∩ s.support.toFinset=T.rootTailHeads root s := by
  classical
  have hs := (allowed_append _ _ _).mp hq |>.2
  ext t
  constructor
  · intro ht
    obtain ⟨htP,htS⟩ := Finset.mem_inter.mp ht
    obtain ⟨_c,_hc,_he,_hl,_hr,_hf,hip,_htW,_he'⟩ :=
      T.rootTailHeads_spec hH hrootb (p.append s) hq htP
    obtain ⟨c,hc⟩ := T.important_covered hip
    have he : entry T.chains root c=t := by simpa only [first,hc] using (T.important_spec hip).2
    exact Finset.mem_image.mpr
      ⟨c,(T.mem_chainSet s c).mpr ⟨t,List.mem_toFinset.mp htS,hc⟩,he⟩
  · intro ht
    obtain ⟨c,hc,he⟩ := Finset.mem_image.mp ht
    have hc' : c ∈ T.chainSet (p.append s) := by rw [T.chainSet_append];exact Finset.mem_union_right _ hc
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨c,hc',he⟩,T.rootTailHeads_physical hH s hs hw ht⟩

/-- Noninitial integer levels yield actual distinct endpoint choices and
EXACT prefix/remaining-target counts on the unchanged fixed-ROOT minimum.
TakeUntil is compared in the SAME filter with the witnessed indexed prefix. -/
theorem fixedRootSuffix_level_split {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root v W : V} (q : DWalk v W)
    (hv : (root,v) ∈ T.important) (hmin : T.FixedRootSuffixMinimum H root q)
    (ell : ℕ) (hell : 2≤ell) (hellq : ell≤T.count q) :
    ∃ (w : V) (hwQ : w ∈ q.support), (root,w) ∈ T.important ∧ w≠v ∧
      T.count (q.takeUntil w hwQ)=ell ∧
      (T.rootTailHeads root q ∩ (q.dropUntil w hwQ).support.toFinset).card+ell=T.count q+1 := by
  classical
  have hrootv := (T.important_spec hv).1
  obtain ⟨i,_hil,hcount,hw⟩ := T.rootSuffix_exists_important_prefix_count hH hrootv q hmin.1 ell hell hellq
  let w := q.getVert i
  have hwQ : w ∈ q.support := q.getVert_mem_support i
  let r := q.takeUntil w hwQ
  let s := q.dropUntil w hwQ
  have he : r.append s=q := q.take_spec hwQ
  have hmrs : T.FixedRootSuffixMinimum H root (r.append s) := by simpa only [he] using hmin
  have hmr := T.fixedRootSuffixMinimum_prefix hH hrootv r s hmrs
  have hmis : T.FixedRootSuffixMinimum H root ((q.take i).append (q.drop i)) := by
    simpa only [Walk.append_take_drop_eq] using hmin
  have hmi := T.fixedRootSuffixMinimum_prefix hH hrootv (q.take i) (q.drop i) hmis
  have hrho : T.count r=ell := by
    have hle := hmr.2 (q.take i) hmi.1
    have hge := hmi.2 r hmr.1
    omega
  have hne : w≠v := by
    intro hew
    obtain ⟨c,hc⟩ := T.important_covered hv
    let n : DWalk v w := (.nil : DWalk v v).copy rfl hew.symm
    have hn : Allowed (T.graph H root) n := by simp [n,Allowed]
    have hcNil : T.count n=1 := by
      unfold count
      rw [show T.chainSet n=T.chainSet (.nil : DWalk v v) from T.chainSet_copy _ rfl hew.symm]
      simp [chainSet,hc]
    have hnil := hmr.2 n hn
    rw [hcNil] at hnil
    omega
  have htargets := T.rootTailHeads_suffix_targets hH hrootv r s hmrs.1 hw
  have hs := (allowed_append _ _ _).mp hmrs.1 |>.2
  have hc := T.count_append_exact hH r s (T.allowed_rebase hH hrootv (r.append s) hmrs.1)
  obtain ⟨cw,hwc⟩ := T.important_covered hw
  change label T.chains w = some cw at hwc
  simp only [hwc,Option.toFinset_some,Finset.card_singleton] at hc
  have hcard := T.rootTailHeads_card hH (T.important_spec hw).1 s hs
  refine ⟨w,hwQ,hw,hne,hrho,?_⟩
  change (T.rootTailHeads root q ∩ s.support.toFinset).card + ell = T.count q + 1
  have htargets' : T.rootTailHeads root q ∩ s.support.toFinset = T.rootTailHeads root s := by
    simpa only [he] using htargets
  rw [htargets',hcard]
  rw [he] at hc
  omega

end GreedyShortcuts.ChainDistance.Context
