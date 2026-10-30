import GreedyShortcuts.ChainOriginalOwnerTailExterior

/-! SOURCE ONLY, UNCOMPILED. Genuine noninitial ROOT heads on the literal
tail, exact fixed-source interior insertion and one-row demand prices.
Admission is proved in the ORIGINAL owner filter, not a rebased optimum. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- Every head OTHER than the initial projection is its actual first
physical entry on this ROOT-admitted tail. The initial guard is excluded. -/
theorem rootTailHead_nonmarker_physical {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root b W v : V}
    (hrootb : Reachable T.G root b) (q : DWalk b W)
    (hq : Allowed (T.graph H root) q) (hv : v ∈ T.rootTailHeads root q)
    (hne : v≠first T.chains root b) :
    q.getVert (T.rootTailHeadPosition root q v)=v ∧ v ∈ q.support := by
  classical
  let i := T.rootTailHeadPosition root q v
  have hi := T.rootTailHeadPosition_spec q hv
  have hibound : i ≤ q.length := hi.1
  have hpos : 0 < i := by
    by_contra hn
    have he : i=0 := by omega
    have hf := hi.2.2
    change first T.chains root (q.getVert i)=v at hf
    rw [he,Walk.getVert_zero] at hf
    exact hne hf.symm
  have he : i-1+1=i := by omega
  have hdiff : label T.chains (q.getVert (i-1))≠label T.chains (q.getVert i) := by
    intro hs
    have hc : label T.chains (q.getVert (i-1))≠none := by
      rw [hs]
      exact hi.2.1
    have hf : first T.chains root (q.getVert (i-1))=v :=
      (first_constant T.chains root _ _ hs).trans hi.2.2
    have hbefore : T.RootTailHeadAt root q v (i-1) := ⟨by omega,hc,hf⟩
    have hle := T.rootTailHeadPosition_le q hbefore
    change i ≤ i-1 at hle
    omega
  have hedge := allowed_vertex_step q hq (i-1) (by omega : i-1<q.length)
  rw [he] at hedge
  have hfirst := hedge.2.resolve_left hdiff |>.resolve_left hi.2.1
  have hv' : q.getVert i=v := hfirst.symm.trans hi.2.2
  exact ⟨hv',hv' ▸ q.getVert_mem_support i⟩

theorem important_from_root_and_actual_access {root x t : V}
    (hrootx : Reachable T.G root x) (hxt : Reachable T.G x t)
    (hip : (root,t) ∈ T.important) : (x,t) ∈ T.important := by
  obtain ⟨c,hc⟩ := T.important_covered hip
  have hf := T.first_inherits hrootx hxt (by simp [hc]) (T.important_spec hip).2
  simpa only [hf] using T.first_important hxt hc

/-- Original reachability places a later vertex in the ACTUAL suffix,
including equality at the joining vertex. No source/filter change occurs. -/
theorem actual_forward_mem_dropUntil {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {src b W a v : V} (q : DWalk b W)
    (hq : Allowed (T.graph H src) q) (ha : a ∈ q.support) (hv : v ∈ q.support)
    (hav : Reachable T.G a v) : v ∈ (q.dropUntil a ha).support := by
  let p := q.takeUntil a ha
  let s := q.dropUntil a ha
  have hm : v ∈ (p.append s).support := by
    simpa only [p,s,q.take_spec ha] using hv
  rcases (Walk.mem_support_append_iff p s).mp hm with hp|hs
  · have hva : Reachable T.G v a :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        ⟨p.dropUntil v hp,allowed_mono (fun _ _ h => h.1)
          (allowed_subwalk (allowed_subwalk hq (q.isSubwalk_takeUntil ha))
            (p.isSubwalk_dropUntil hp))⟩
    have he : a=v := (GreedyShortcuts.CanonicalSegments.acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ hav hva
    simpa only [he] using s.start_mem_support
  · exact hs

theorem actual_backward_mem_takeUntil {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {src a W b v : V} (q : DWalk a W)
    (hq : Allowed (T.graph H src) q) (hb : b ∈ q.support) (hv : v ∈ q.support)
    (hvb : Reachable T.G v b) : v ∈ (q.takeUntil b hb).support := by
  let p := q.takeUntil b hb
  let s := q.dropUntil b hb
  have hm : v ∈ (p.append s).support := by
    simpa only [p,s,q.take_spec hb] using hv
  rcases (Walk.mem_support_append_iff p s).mp hm with hp|hs
  · exact hp
  · have hbv : Reachable T.G b v :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        ⟨s.takeUntil v hs,allowed_mono (fun _ _ h => h.1)
          (allowed_subwalk (allowed_subwalk hq (q.isSubwalk_dropUntil hb))
            (s.isSubwalk_takeUntil hs))⟩
    have he : v=b := (GreedyShortcuts.CanonicalSegments.acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ hvb hbv
    simpa only [he] using p.end_mem_support

/-- The literal inserted dart respects THIS original source's first test.
Its source endpoint need not be that objective source. -/
theorem important_target_inserted_dart (H : Finset (V × V)) {x a b : V}
    (hb : (x,b) ∈ T.important) : T.graph (insert (a,b) H) x a b := by
  exact ⟨Or.inr (Finset.mem_union_right _ (Finset.mem_insert_self _ _)),
    Or.inr (Or.inr (T.important_spec hb).2)⟩

/-- Real interior shortcut on ONE unchanged x-minimum. Its OLD segment
count and both covered joins are explicit; no subpath optimum at a is used. -/
theorem tail_interior_insertion_saving {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {x a b t : V}
    (p : DWalk x a) (r : DWalk a b) (q : DWalk b t)
    (hall : Allowed (T.graph H x) ((p.append r).append q))
    (hmin : T.count ((p.append r).append q)=T.distance H x t)
    (ha : label T.chains a≠none) (hb : (x,b) ∈ T.important) (hne : a≠b) :
    (a,b) ∈ candidates T.G ∧ T.graph (insert (a,b) H) x a b ∧
      T.distance (insert (a,b) H) x t+T.count r≤T.distance H x t+2 := by
  classical
  obtain ⟨hpr,hq⟩ := (allowed_append _ _ _).mp hall
  obtain ⟨hp,hr⟩ := (allowed_append _ _ _).mp hpr
  obtain ⟨c,hac⟩ := Option.ne_none_iff_exists'.mp ha
  obtain ⟨d,hbc⟩ := T.important_covered hb
  have hab : Reachable T.G a b :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨r,allowed_mono (fun _ _ h => h.1) hr⟩
  have hxt : Reachable T.G x t :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨(p.append r).append q,allowed_mono (fun _ _ h => h.1) hall⟩
  have hdart := T.important_target_inserted_dart H (a := a) hb
  let short : DWalk a b := .cons (by simpa using hne) .nil
  have hshort : Allowed (T.graph (insert (a,b) H) x) short :=
    (allowed_cons _ _ _).mpr ⟨hdart,allowed_nil _ _⟩
  have hshortCount : T.count short≤2 := by
    simpa only [short,Walk.length_cons,Walk.length_nil] using T.count_le_vertices short
  have hp' := allowed_mono (T.graph_mono (Finset.subset_insert (a,b) H) x) hp
  have hq' := allowed_mono (T.graph_mono (Finset.subset_insert (a,b) H) x) hq
  have hnew := T.distance_le_walk (insert (a,b) H) hxt ((p.append short).append q)
    ((allowed_append _ _ _).mpr ⟨(allowed_append _ _ _).mpr ⟨hp',hshort⟩,hq'⟩)
  have hn1 := T.count_append_covered p short hac
  have hn2 := T.count_append_covered (p.append short) q hbc
  have ho1 := T.count_append_exact hH p r hpr
  have ho2 := T.count_append_exact hH (p.append r) q hall
  simp only [hac,hbc,Option.toFinset_some,Finset.card_singleton] at ho1 ho2
  exact ⟨(mem_candidates T.G _).mpr ⟨hne,hab⟩,hdart,by omega⟩

/-- ALL actual suffix targets receive this SAME interior edge offer. Old
prefix optimality is applied only in the unchanged source x filter. -/
theorem interior_insertion_suffix_saving {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {x a b W : V}
    (p : DWalk x a) (r : DWalk a b) (s : DWalk b W)
    (hall : Allowed (T.graph H x) ((p.append r).append s))
    (hmin : T.count ((p.append r).append s)=T.distance H x W)
    (ha : label T.chains a≠none) (hb : (x,b) ∈ T.important) (hne : a≠b)
    {t : V} (ht : t ∈ s.support) :
    T.distance (insert (a,b) H) x t+T.count r≤T.distance H x t+2 := by
  let l := s.takeUntil t ht
  let u := s.dropUntil t ht
  have he : (((p.append r).append l).append u)=(p.append r).append s := by
    dsimp only [l,u]
    rw [← Walk.append_assoc,s.take_spec ht]
  have hfull : Allowed (T.graph H x) (((p.append r).append l).append u) := by
    simpa only [he] using hall
  have hfullMin : T.count (((p.append r).append l).append u)=T.distance H x W := by
    simpa only [he] using hmin
  have hprefix := T.minimum_prefix hH ((p.append r).append l) u hfull hfullMin
  exact (T.tail_interior_insertion_saving hH p r l ((allowed_append _ _ _).mp hfull).1
    hprefix ha hb hne).2.2

end GreedyShortcuts.ChainDistance.Context
