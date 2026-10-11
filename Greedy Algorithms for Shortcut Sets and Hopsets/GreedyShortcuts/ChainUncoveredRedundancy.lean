import GreedyShortcuts.ChainPositiveChoices

/-! Endpoint-saturated uncovered destinations are also globally redundant.
This completes a necessary own-distance test for every positive legal choice;
it supplies no quantitative bound on the remaining positive candidates. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst CanonicalSegments ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- A saturated route ending outside the cover has no covered label except
possibly its start label. Original-source validity and DAG antisymmetry forbid
re-entry into that label, so the route is valid for every source filter. -/
theorem uncovered_saturated_route_transfer {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {u v : V} (hv : label T.chains v=none)
    (q : DWalk u v) (hq : Allowed (T.graph H u) q)
    (hcount : T.count q=T.endpointFloor u v) (s : V) :
    Allowed (T.graph H s) q := by
  classical
  have hset := T.chainSet_eq_endpoints_of_saturated q hcount
  intro d hd
  have hh := hq d hd
  refine ⟨hh.1,?_⟩
  rcases hh.2 with he | hn | hf
  · exact Or.inl he
  · exact Or.inr (Or.inl hn)
  · by_cases hn : label T.chains d.snd=none
    · exact Or.inr (Or.inl hn)
    obtain ⟨c,hc⟩ := Option.ne_none_iff_exists'.mp hn
    have hmem : c∈T.chainSet q := (T.mem_chainSet q c).mpr
      ⟨d.snd,q.dart_snd_mem_support_of_mem_darts hd,hc⟩
    have hu : label T.chains u=some c := by simpa [hset,hv] using hmem
    have hfirst := (first_constant T.chains u d.snd u (hc.trans hu.symm)).trans (T.first_self u)
    have hdu : d.snd=u := hf.symm.trans hfirst
    have hr : Reachable T.G u d.fst :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        ⟨q.takeUntil d.fst (q.dart_fst_mem_support_of_mem_darts hd),
          allowed_mono (fun _ _ h => h.1) (allowed_subwalk hq
            (q.isSubwalk_takeUntil (q.dart_fst_mem_support_of_mem_darts hd)))⟩
    have he : Reachable T.G d.fst u := by
      have h := (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        (reachable_edge hh.1)
      simpa only [hdu] using h
    have huf := (acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ hr he
    exact (d.fst_ne_snd (huf.symm.trans hdu.symm)).elim

/-- An originally reachable saturated uncovered pair can be inserted without
changing any normalized distance, using literal old-route substitution. -/
theorem distance_insert_uncovered_saturated_eq {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {u v : V} (huv : Reachable T.G u v)
    (hv : label T.chains v=none) (hsat : T.distance H u v=T.endpointFloor u v)
    (s t : V) : T.distance (insert (u,v) H) s t=T.distance H s t := by
  classical
  apply Nat.le_antisymm (T.distance_antitone s t (Finset.subset_insert _ _))
  by_cases hr : Reachable T.G s t
  · obtain ⟨q,hq,hqc⟩ := T.distance_spec H huv
    obtain ⟨p,hp,hpc⟩ := T.distance_spec (insert (u,v) H) hr
    have hcount := hqc.trans hsat
    obtain ⟨r,hrvalid,hsub⟩ := T.eliminate_label_redundant_edge H q
      (T.uncovered_saturated_route_transfer hH hv q hq hcount s)
      (T.chainSet_eq_endpoints_of_saturated q hcount).le p hp
    exact (T.distance_le_walk H hr r hrvalid).trans ((Finset.card_le_card hsub).trans_eq hpc)
  · simp [distance,hr]

theorem potential_insert_uncovered_saturated_eq {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {u v : V} (huv : Reachable T.G u v)
    (hv : label T.chains v=none) (hsat : T.distance H u v=T.endpointFloor u v) :
    T.potential (insert (u,v) H)=T.potential H := by
  apply Finset.sum_congr rfl
  intro st _
  exact T.distance_insert_uncovered_saturated_eq hH huv hv hsat st.1 st.2

/-- Every positive legal raw-saving candidate has strictly positive excess
in its own original-source normalized metric, including uncovered heads. -/
theorem positive_choice_own_excess {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {u v : V} (he : (u,v)∈candidates T.G)
    (hdrop : T.potential (insert (u,v) H)<T.potential H) :
    T.endpointFloor u v<T.distance H u v := by
  classical
  by_cases hv : label T.chains v=none
  · have hr : Reachable T.G u v := (Finset.mem_filter.mp he).2.2
    have hlo := T.endpointFloor_le_distance H hr
    by_contra hn
    have hs : T.distance H u v=T.endpointFloor u v := by omega
    exact (Nat.ne_of_lt hdrop) (T.potential_insert_uncovered_saturated_eq hH hr hv hs)
  · exact (Finset.mem_filter.mp (T.positive_covered_choice hH he hv hdrop)).2

/-- Saturation is a permanent raw-candidate retirement certificate for any
legal candidate, not only for original important pairs. -/
theorem legal_saturated_edge_stays_redundant {H J : Finset (V × V)}
    (hJ : J ⊆ candidates T.G) (hHJ : H ⊆ J) {u v : V}
    (he : (u,v)∈candidates T.G) (hsat : T.distance H u v=T.endpointFloor u v) :
    T.potential (insert (u,v) J)=T.potential J := by
  classical
  apply Nat.le_antisymm (T.potential_antitone (Finset.subset_insert _ _))
  by_contra hn
  have hd : T.potential (insert (u,v) J)<T.potential J := by omega
  have hpos := T.positive_choice_own_excess hJ he hd
  have hsatJ : T.distance J u v=T.endpointFloor u v :=
    T.saturated_mono hHJ (Finset.mem_filter.mp he).2.2 hsat
  exact (Nat.ne_of_gt hpos) hsatJ

end GreedyShortcuts.ChainDistance.Context
