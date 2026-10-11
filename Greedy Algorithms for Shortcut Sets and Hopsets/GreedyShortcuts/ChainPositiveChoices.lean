import GreedyShortcuts.ChainInternalRedundancy

/-! Actual positive-saving interchain choices with covered destinations.
Uncovered destinations remain a separate candidate domain. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst CanonicalSegments ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- Strict raw improvement has a concrete strictly improved important demand. -/
theorem exists_improved_pair {H : Finset (V × V)} {e : V × V}
    (hdrop : T.potential (insert e H)<T.potential H) :
    ∃ st∈T.important,T.distance (insert e H) st.1 st.2<T.distance H st.1 st.2 := by
  classical
  by_contra hn
  push Not at hn
  have hle : T.potential H ≤ T.potential (insert e H) := Finset.sum_le_sum (fun st hs => hn st hs)
  omega

/-- A used interchain insertion into a covered chain must itself be an
important edge: first-entry inheritance follows the actual improved route. -/
theorem improving_interchain_edge_important {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {u v s t : V} (he : (u,v)∈candidates T.G)
    (hv : label T.chains v≠none) (hlabels : label T.chains u≠label T.chains v)
    (hst : (s,t)∈T.important)
    (hdrop : T.distance (insert (u,v) H) s t<T.distance H s t) :
    (u,v)∈T.important := by
  classical
  have hlegal : insert (u,v) H ⊆ candidates T.G := Finset.insert_subset he hH
  have hr := (T.important_spec hst).1
  obtain ⟨p,hp,hpc⟩ := T.distance_spec (insert (u,v) H) hr
  have hbad : ¬Allowed (T.graph H s) p := by
    intro hh
    have hb := T.distance_le_walk H hr p hh
    omega
  simp only [Allowed,not_forall] at hbad
  obtain ⟨dart,hmem,hnot⟩ := hbad
  have hstep := hp dart hmem
  have hedge : (dart.fst,dart.snd)=(u,v) := by
    rcases hstep.1 with hg | hh
    · exact (hnot ⟨Or.inl hg,hstep.2⟩).elim
    rcases Finset.mem_union.mp hh with hb | hi
    · exact (hnot ⟨Or.inr (Finset.mem_union_left _ hb),hstep.2⟩).elim
    rcases Finset.mem_insert.mp hi with heq | hm
    · exact heq
    · exact (hnot ⟨Or.inr (Finset.mem_union_right _ hm),hstep.2⟩).elim
  have hfst : dart.fst=u := congrArg Prod.fst hedge
  have hsnd : dart.snd=v := congrArg Prod.snd hedge
  have hsuv : Reachable T.G s dart.fst :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hlegal) _ _).mp
      ⟨p.takeUntil dart.fst (p.dart_fst_mem_support_of_mem_darts hmem),
        allowed_mono (fun _ _ h => h.1) (allowed_subwalk hp
          (p.isSubwalk_takeUntil (p.dart_fst_mem_support_of_mem_darts hmem)))⟩
  have hsu : Reachable T.G s u := by simpa only [hfst] using hsuv
  have huv := (Finset.mem_filter.mp he).2.2
  have hf : first T.chains s v=v := by
    have hh := hstep.2
    rw [hfst,hsnd] at hh
    exact hh.resolve_left hlabels |>.resolve_left hv
  obtain ⟨c,hc⟩ := Option.ne_none_iff_exists'.mp hv
  have hsvp : (s,v)∈T.important := by
    simpa only [hf] using T.first_important (reachable_trans hsu huv) hc
  exact T.important_inherits hsvp hsu huv

/-- Such a positive raw-saving candidate belongs to the actual unsaturated
important set. Its tail may be uncovered; only destination and label change
are needed in addition to legality and actual strict raw improvement. -/
theorem positive_interchain_covered_choice {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {u v : V} (he : (u,v)∈candidates T.G)
    (hv : label T.chains v≠none) (hlabels : label T.chains u≠label T.chains v)
    (hdrop : T.potential (insert (u,v) H)<T.potential H) : (u,v)∈T.unsaturated H := by
  obtain ⟨st,hst,hd⟩ := T.exists_improved_pair hdrop
  exact T.positive_important_edge_unsaturated hH
    (T.improving_interchain_edge_important hH he hv hlabels hst hd) hdrop

/-- A precise remaining-domain split for all actual positive legal insertions.
This theorem does not discard the uncovered-target or same-label alternatives. -/
theorem positive_choice_domain {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {u v : V} (he : (u,v)∈candidates T.G)
    (hdrop : T.potential (insert (u,v) H)<T.potential H) :
    label T.chains v=none ∨ label T.chains u=label T.chains v ∨ (u,v)∈T.unsaturated H := by
  by_cases hv : label T.chains v=none
  · exact Or.inl hv
  by_cases heq : label T.chains u=label T.chains v
  · exact Or.inr (Or.inl heq)
  exact Or.inr (Or.inr (T.positive_interchain_covered_choice hH he hv heq hdrop))

/-- Actual preprocessing rules out the same-label alternative. Every legal
positive insertion with a covered head is an unsaturated important candidate. -/
theorem positive_covered_choice {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {u v : V} (he : (u,v)∈candidates T.G) (hv : label T.chains v≠none)
    (hdrop : T.potential (insert (u,v) H)<T.potential H) : (u,v)∈T.unsaturated H := by
  classical
  have hlabels : label T.chains u≠label T.chains v := by
    intro heq
    obtain ⟨c,hc⟩ := Option.ne_none_iff_exists'.mp hv
    have hzero : T.potential (insert (u,v) H)=T.potential H :=
      T.potential_insert_internal_eq H (Finset.mem_filter.mp he).2.2 (heq.trans hc) hc
    exact (Nat.ne_of_lt hdrop) hzero
  exact T.positive_interchain_covered_choice hH he hv hlabels hdrop

/-- A complete dichotomy for positive legal choices: uncovered destination,
or a genuinely unsaturated important edge. No discarded candidate oracle. -/
theorem positive_choice_uncovered_or_unsaturated {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {u v : V} (he : (u,v)∈candidates T.G)
    (hdrop : T.potential (insert (u,v) H)<T.potential H) :
    label T.chains v=none ∨ (u,v)∈T.unsaturated H := by
  by_cases hv : label T.chains v=none
  · exact Or.inl hv
  exact Or.inr (T.positive_covered_choice hH he hv hdrop)

end GreedyShortcuts.ChainDistance.Context
