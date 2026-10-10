import GreedyShortcuts.ChainSaturatedTransport

/-! A source-capacity restriction on genuinely short-demand savings.
This does not prove cubic progress or a nearlinear stopping bound. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst CanonicalSegments ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- An interchain dart on a saturated valid route has the source chain as
its tail label and the target chain as its head label. -/
theorem saturated_dart_labels {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (p : DWalk s t) (hp : Allowed (T.graph H s) p)
    (hcount : T.count p = T.endpointFloor s t)
    (e : (⊤ : SimpleGraph V).Dart) (he : e ∈ p.darts) {c d : I}
    (hc : label T.chains e.fst = some c) (hd : label T.chains e.snd = some d)
    (hcd : c ≠ d) : label T.chains s = some c ∧ label T.chains t = some d := by
  classical
  have hset := T.chainSet_eq_endpoints_of_saturated p hcount
  have htail : label T.chains s = some c ∨ label T.chains t = some c := by
    have hm := (T.mem_chainSet p c).mpr ⟨_,p.dart_fst_mem_support_of_mem_darts he,hc⟩
    rw [hset] at hm
    simpa using hm
  have hhead : label T.chains s = some d ∨ label T.chains t = some d := by
    have hm := (T.mem_chainSet p d).mpr ⟨_,p.dart_snd_mem_support_of_mem_darts he,hd⟩
    rw [hset] at hm
    simpa using hm
  have hnot : label T.chains s ≠ some d := by
    intro hs
    have hh := hp e he
    have hlabels : label T.chains e.fst ≠ label T.chains e.snd := by
      rw [hc,hd]
      exact fun h => hcd (Option.some.inj h)
    have hfirst : first T.chains s e.snd = e.snd :=
      hh.2.resolve_left hlabels |>.resolve_left (by simp [hd])
    have hsame := (first_constant T.chains s e.snd s (hd.trans hs.symm)).trans (T.first_self s)
    have hes : e.snd = s := hfirst.symm.trans hsame
    have hsu : Reachable T.G s e.fst :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        ⟨p.takeUntil e.fst (p.dart_fst_mem_support_of_mem_darts he),
          allowed_mono (fun _ _ h => h.1) (allowed_subwalk hp
            (p.isSubwalk_takeUntil (p.dart_fst_mem_support_of_mem_darts he)))⟩
    have hus : Reachable T.G e.fst s := by
      rw [←hes]
      exact (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp (reachable_edge hh.1)
    have hse := (acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ hsu hus
    have heq : some c = some d := hc.symm.trans ((congrArg (label T.chains) hse.symm).trans hs)
    exact hcd (Option.some.inj heq)
  have ht := hhead.resolve_left hnot
  refine ⟨htail.resolve_right ?_,ht⟩
  intro htc
  exact hcd (Option.some.inj (htc.symm.trans ht))

/-- Any strict improvement of an old distance at most three, with distinct
covered endpoint labels, is a single unit and is sourced on the edge's tail
chain. No assumption of source-independent shortest paths is used. -/
theorem short_improvement_labels {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {u v s t : V} {c d : I} (he : (u,v) ∈ candidates T.G)
    (hu : label T.chains u = some c) (hv : label T.chains v = some d) (hcd : c ≠ d)
    (hst : (s,t) ∈ T.important) (hfloor : T.endpointFloor s t = 2)
    (hold : T.distance H s t ≤ 3)
    (hdrop : T.distance (insert (u,v) H) s t < T.distance H s t) :
    label T.chains s = some c ∧ label T.chains t = some d ∧
      T.distance H s t - T.distance (insert (u,v) H) s t = 1 := by
  classical
  have hlegal : insert (u,v) H ⊆ candidates T.G := Finset.insert_subset he hH
  have hr := (T.important_spec hst).1
  have hlo := T.endpointFloor_le_distance (insert (u,v) H) hr
  have hnew : T.distance (insert (u,v) H) s t = 2 := by omega
  obtain ⟨p,hp,hpc⟩ := T.distance_spec (insert (u,v) H) hr
  have hbad : ¬Allowed (T.graph H s) p := by
    intro hh
    have hb := T.distance_le_walk H hr p hh
    omega
  simp only [Allowed,not_forall] at hbad
  obtain ⟨dart,hmem,hnot⟩ := hbad
  have hstep := hp dart hmem
  have hedge : (dart.fst,dart.snd) = (u,v) := by
    rcases hstep.1 with hg | hh
    · exact (hnot ⟨Or.inl hg,hstep.2⟩).elim
    rcases Finset.mem_union.mp hh with hb | hi
    · exact (hnot ⟨Or.inr (Finset.mem_union_left _ hb),hstep.2⟩).elim
    rcases Finset.mem_insert.mp hi with heq | hmem
    · exact heq
    · exact (hnot ⟨Or.inr (Finset.mem_union_right _ hmem),hstep.2⟩).elim
  have hfst : dart.fst = u := congrArg Prod.fst hedge
  have hsnd : dart.snd = v := congrArg Prod.snd hedge
  have hh := T.saturated_dart_labels hlegal p hp (by omega) dart hmem
    (by simpa only [hfst] using hu) (by simpa only [hsnd] using hv) hcd
  exact ⟨hh.1,hh.2,by omega⟩

/-- All floor-two, distance-at-most-three demands together contribute at
most the actual number of vertices on the inserted edge's tail chain. -/
theorem short_drop_le_tail_size {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {u v : V} {c d : I} (he : (u,v) ∈ candidates T.G)
    (hu : label T.chains u = some c) (hv : label T.chains v = some d) (hcd : c ≠ d)
    (A : Finset (V × V)) (hA : A ⊆ T.important)
    (hf : ∀ st∈A,T.endpointFloor st.1 st.2 = 2)
    (hd : ∀ st∈A,T.distance H st.1 st.2 ≤ 3) :
    (∑ st∈A,(T.distance H st.1 st.2-T.distance (insert (u,v) H) st.1 st.2)) ≤
      (T.chains c).length := by
  classical
  let B := A.filter (fun st => T.distance (insert (u,v) H) st.1 st.2 < T.distance H st.1 st.2)
  have hB : B ⊆ A := Finset.filter_subset _ _
  have facts : ∀ st∈B,label T.chains st.1 = some c ∧ label T.chains st.2 = some d ∧
      T.distance H st.1 st.2-T.distance (insert (u,v) H) st.1 st.2 = 1 := by
    intro st hs
    have hb := Finset.mem_filter.mp hs
    exact T.short_improvement_labels hH he hu hv hcd (hA hb.1) (hf st hb.1) (hd st hb.1) hb.2
  have hsum : (∑ st∈A,(T.distance H st.1 st.2-T.distance (insert (u,v) H) st.1 st.2)) = B.card := by
    calc
      _ = ∑ st∈B,(T.distance H st.1 st.2-T.distance (insert (u,v) H) st.1 st.2) := by
        symm
        apply Finset.sum_subset hB
        intro st hs hn
        have hh : ¬T.distance (insert (u,v) H) st.1 st.2 < T.distance H st.1 st.2 := by
          intro hh
          exact hn (Finset.mem_filter.mpr ⟨hs,hh⟩)
        omega
      _ = ∑ _st∈B,1 := Finset.sum_congr rfl (fun st hs => (facts st hs).2.2)
      _ = B.card := by simp
  have hsub : B ⊆ (T.chains c).support.image (fun s => (s,entry T.chains s d)) := by
    intro st hs
    have hlabels := facts st hs
    have hi := (T.important_spec (hA (hB hs))).2
    have ht : entry T.chains st.1 d = st.2 := by
      simpa only [first,hlabels.2.1] using hi
    exact Finset.mem_image.mpr ⟨st.1,mem_of_label T.chains hlabels.1,Prod.ext rfl ht⟩
  rw [hsum]
  calc
    _ ≤ ((T.chains c).support.image (fun s => (s,entry T.chains s d))).card := Finset.card_le_card hsub
    _ ≤ (T.chains c).support.card := Finset.card_image_le
    _ = _ := ChainUnion.Chain.support_card _

end GreedyShortcuts.ChainDistance.Context
