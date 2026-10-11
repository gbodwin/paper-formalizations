import GreedyShortcuts.ChainUncoveredRedundancy

/-! A positive insertion can improve a target only if the insertion's own
source has an unsaturated important demand to that same literal target. This
is a support statement, with no transfer of positive-excess minima. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst CanonicalSegments ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- Once the tail-to-target demand is saturated, the old route can replace
an entire suffix beginning at the inserted edge, rather than that edge alone. -/
theorem eliminate_edge_with_saturated_tail_target {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {u v s t : V}
    (hst : (s,t)∈T.important) (hut : (u,t)∈T.important)
    (hsat : T.distance H u t=T.endpointFloor u t)
    {a : V} (p : DWalk a t) (hp : Allowed (T.graph (insert (u,v) H) s) p) :
    ∃ r : DWalk a t,Allowed (T.graph H s) r ∧ T.chainSet r ⊆ T.chainSet p := by
  classical
  obtain ⟨q,hq,hqc⟩ := T.distance_spec H (T.important_spec hut).1
  have hqs := T.saturated_route_transfer_legal hH hst hut q hq (hqc.trans hsat)
  have hset := T.chainSet_eq_endpoints_of_saturated q (hqc.trans hsat)
  revert hp
  induction p with
  | nil => intro _; exact ⟨.nil,allowed_nil _ _,Finset.Subset.refl _⟩
  | @cons a b t hab p ih =>
    intro hp
    obtain ⟨hedge,hp⟩ := (allowed_cons _ hab p).mp hp
    by_cases he : (a,b)=(u,v)
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      refine ⟨q,hqs,?_⟩
      intro c hc
      rw [hset] at hc
      rcases Finset.mem_union.mp hc with hc | hc
      · exact (T.mem_chainSet (.cons hab p) c).mpr
          ⟨a,by simp,by simpa using hc⟩
      · exact (T.mem_chainSet (.cons hab p) c).mpr
          ⟨t,SimpleGraph.Walk.end_mem_support _,by simpa using hc⟩
    · have hold : T.graph H s a b := by
        refine ⟨?_,hedge.2⟩
        rcases hedge.1 with hg | hh
        · exact Or.inl hg
        rcases Finset.mem_union.mp hh with hb | hi
        · exact Or.inr (Finset.mem_union_left _ hb)
        exact Or.inr (Finset.mem_union_right _ ((Finset.mem_insert.mp hi).resolve_left he))
      obtain ⟨tail,htail,hsub⟩ := ih hst hut hsat q hq hqc hqs hset hp
      refine ⟨.cons hab tail,(allowed_cons _ _ _).mpr ⟨hold,htail⟩,?_⟩
      let one : DWalk a b := .cons hab .nil
      change T.chainSet (one.append tail) ⊆ T.chainSet (one.append p)
      rw [T.chainSet_append,T.chainSet_append]
      exact Finset.union_subset_union (Finset.Subset.refl _) hsub

/-- Saturation of the tail's demand to this same important target prevents
any improvement of that target in another original source convention. -/
theorem distance_insert_eq_of_tail_target_saturated {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {u v s t : V}
    (hst : (s,t)∈T.important) (hut : (u,t)∈T.important)
    (hsat : T.distance H u t=T.endpointFloor u t) :
    T.distance (insert (u,v) H) s t=T.distance H s t := by
  classical
  apply Nat.le_antisymm (T.distance_antitone s t (Finset.subset_insert _ _))
  obtain ⟨p,hp,hpc⟩ := T.distance_spec (insert (u,v) H) (T.important_spec hst).1
  obtain ⟨r,hr,hsub⟩ := T.eliminate_edge_with_saturated_tail_target hH hst hut hsat p hp
  exact (T.distance_le_walk H (T.important_spec hst).1 r hr).trans
    ((Finset.card_le_card hsub).trans_eq hpc)

/-- Any genuinely improved important demand ends at an unsaturated demand
of the inserted edge's tail, even when the inserted head is uncovered. -/
theorem improved_pair_tail_target_unsaturated {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {u v s t : V} (he : (u,v)∈candidates T.G)
    (hst : (s,t)∈T.important)
    (hdrop : T.distance (insert (u,v) H) s t<T.distance H s t) :
    (u,t)∈T.unsaturated H := by
  classical
  have hlegal : insert (u,v) H ⊆ candidates T.G := Finset.insert_subset he hH
  obtain ⟨p,hp,hpc⟩ := T.distance_spec (insert (u,v) H) (T.important_spec hst).1
  have hbad : ¬Allowed (T.graph H s) p := by
    intro hh
    have hb := T.distance_le_walk H (T.important_spec hst).1 p hh
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
  have hsu' : Reachable T.G s dart.fst :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hlegal) _ _).mp
      ⟨p.takeUntil dart.fst (p.dart_fst_mem_support_of_mem_darts hmem),
        allowed_mono (fun _ _ h => h.1) (allowed_subwalk hp
          (p.isSubwalk_takeUntil (p.dart_fst_mem_support_of_mem_darts hmem)))⟩
  have hut' : Reachable T.G dart.fst t :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hlegal) _ _).mp
      ⟨p.dropUntil dart.fst (p.dart_fst_mem_support_of_mem_darts hmem),
        allowed_mono (fun _ _ h => h.1) (allowed_subwalk hp
          (p.isSubwalk_dropUntil (p.dart_fst_mem_support_of_mem_darts hmem)))⟩
  have hsu : Reachable T.G s u := by simpa only [hfst] using hsu'
  have hut : Reachable T.G u t := by simpa only [hfst] using hut'
  have hip := T.important_inherits hst hsu hut
  apply Finset.mem_filter.mpr
  refine ⟨hip,?_⟩
  change T.endpointFloor u t<T.distance H u t
  have hlo := T.endpointFloor_le_distance H hut
  by_contra hn
  have hsat : T.distance H u t=T.endpointFloor u t := by omega
  have hz := T.distance_insert_eq_of_tail_target_saturated (v := v) hH hst hip hsat
  exact (Nat.ne_of_lt hdrop) hz

/-- A positive legal raw choice always starts in a currently live original
source row. Saturated padding rows cannot secretly help another source. -/
theorem positive_choice_live_tail {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {u v : V} (he : (u,v)∈candidates T.G)
    (hdrop : T.potential (insert (u,v) H)<T.potential H) :
    ∃ t,(u,t)∈T.unsaturated H := by
  obtain ⟨st,hst,hd⟩ := T.exists_improved_pair hdrop
  exact ⟨st.2,T.improved_pair_tail_target_unsaturated hH he hst hd⟩

/-- A completely endpoint-saturated source row retires every outgoing legal
candidate for the unchanged whole raw potential. -/
theorem potential_insert_eq_of_tail_row_saturated {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {u v : V} (he : (u,v)∈candidates T.G)
    (hrow : ∀ t,(u,t)∈T.important → T.distance H u t=T.endpointFloor u t) :
    T.potential (insert (u,v) H)=T.potential H := by
  classical
  apply Nat.le_antisymm (T.potential_antitone (Finset.subset_insert _ _))
  by_contra hn
  have hd : T.potential (insert (u,v) H)<T.potential H := by omega
  obtain ⟨t,ht⟩ := T.positive_choice_live_tail hH he hd
  have ht' := Finset.mem_filter.mp ht
  exact (Nat.ne_of_gt ht'.2) (hrow t ht'.1)

end GreedyShortcuts.ChainDistance.Context
