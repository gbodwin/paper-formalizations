import GreedyShortcuts.ChainInsertionFrontier

/-! Positive raw insertions retire an actual important demand in their own
source row. The first covered entry handles uncovered inserted destinations. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst CanonicalSegments ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

private theorem chainSet_cons {u v t : V} (h : (⊤ : SimpleGraph V).Adj u v)
    (p : DWalk v t) :
    T.chainSet (.cons h p)=(label T.chains u).toFinset ∪ T.chainSet p := by
  classical
  ext c
  simp only [T.mem_chainSet,Finset.mem_union,Option.mem_toFinset,Walk.support_cons,List.mem_cons]
  aesop

/-- A covered-head candidate that improves raw potential directly saturates
its own important demand, including an uncovered tail. -/
theorem direct_important_candidate_saturated (H : Finset (V × V)) {u v : V}
    (he : (u,v)∈candidates T.G) (hip : (u,v)∈T.important) :
    T.distance (insert (u,v) H) u v=T.endpointFloor u v := by
  classical
  have hne : u≠v := (Finset.mem_filter.mp he).2.1
  let q : DWalk u v := .cons (by simpa using hne) .nil
  have hq : Allowed (T.graph (insert (u,v) H) u) q := by
    refine (allowed_cons _ _ _).mpr ⟨⟨Or.inr ?_,Or.inr (Or.inr (T.important_spec hip).2)⟩,allowed_nil _ _⟩
    exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  apply Nat.le_antisymm _ (T.endpointFloor_le_distance _ (T.important_spec hip).1)
  have hd := T.distance_le_walk _ (T.important_spec hip).1 q hq
  simpa [q,count,chainSet,endpointFloor] using hd

/-- For an uncovered-head insertion, the actual first covered entry after
its literal use becomes saturated in the insertion tail's row and was not
saturated before. Otherwise an old endpoint-only route repairs the whole walk. -/
theorem uncovered_improvement_new_saturation {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {u v s t : V} (he : (u,v)∈candidates T.G)
    (hv : label T.chains v=none) (hst : (s,t)∈T.important)
    (hdrop : T.distance (insert (u,v) H) s t<T.distance H s t) :
    ∃ w,(u,w)∈T.unsaturated H ∧
      T.distance (insert (u,v) H) u w=T.endpointFloor u w := by
  classical
  let J := insert (u,v) H
  change T.distance J s t<T.distance H s t at hdrop
  have hJ : J ⊆ candidates T.G := Finset.insert_subset he hH
  obtain ⟨p,hp,hpc⟩ := T.distance_spec J (T.important_spec hst).1
  have hb : ¬Allowed (T.graph H s) p := by
    intro ho
    have hd := T.distance_le_walk H (T.important_spec hst).1 p ho
    omega
  obtain ⟨h,l,r,hpform,hl,hedge,hr⟩ := T.improved_walk_insertion_decomposition hH he p hp hb
  obtain ⟨ct,hct⟩ := T.important_covered hst
  obtain ⟨w,c,a,b,hrform,hw,haset,hfirst⟩ := T.first_covered_prefix r hr hv (by simp [hct])
  have hab : Allowed (T.graph H s) (a.append b) := by simpa only [←hrform] using hr
  have ha := (allowed_append _ a b).mp hab |>.1
  have hbb := (allowed_append _ a b).mp hab |>.2
  have hsu : Reachable T.G s u :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨l,allowed_mono (fun _ _ h => h.1) hl⟩
  have hvw : Reachable T.G v w :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨a,allowed_mono (fun _ _ h => h.1) ha⟩
  have huw : Reachable T.G u w := reachable_trans (Finset.mem_filter.mp he).2.2 hvw
  have hswp : (s,w)∈T.important := by
    simpa only [hfirst] using T.first_important (reachable_trans hsu huw) hw
  have huwp := T.important_inherits hswp hsu huw
  let q : DWalk u w := .cons h a
  have hqs : Allowed (T.graph J s) q := (allowed_cons _ _ _).mpr
    ⟨hedge,allowed_mono (T.graph_mono (Finset.subset_insert _ _) s) ha⟩
  have hqu := T.allowed_rebase hJ hsu q hqs
  have hqset : T.chainSet q=(label T.chains u).toFinset ∪ (label T.chains w).toFinset := by
    rw [chainSet_cons,haset,hw]
    rfl
  have hqcount : T.count q=T.endpointFloor u w := congrArg Finset.card hqset
  have hnew : T.distance J u w=T.endpointFloor u w :=
    Nat.le_antisymm ((T.distance_le_walk J huw q hqu).trans_eq hqcount)
      (T.endpointFloor_le_distance J huw)
  refine ⟨w,Finset.mem_filter.mpr ⟨huwp,?_⟩,hnew⟩
  change T.endpointFloor u w<T.distance H u w
  have hlo := T.endpointFloor_le_distance H huw
  by_contra hn
  have hsat : T.distance H u w=T.endpointFloor u w := by omega
  obtain ⟨old,hold,hoc⟩ := T.distance_spec H huw
  have holds := T.saturated_route_transfer_legal hH hswp huwp old hold (hoc.trans hsat)
  have holdset : T.chainSet old=T.chainSet q :=
    (T.chainSet_eq_endpoints_of_saturated old (hoc.trans hsat)).trans hqset.symm
  have hall : Allowed (T.graph H s) (l.append (old.append b)) :=
    (allowed_append _ _ _).mpr ⟨hl,(allowed_append _ _ _).mpr ⟨holds,hbb⟩⟩
  have hpform' : p=l.append (q.append b) := by
    simpa only [q,Walk.cons_append] using hpform.trans (congrArg (fun z => l.append (.cons h z)) hrform)
  have hs : T.chainSet (l.append (old.append b))=T.chainSet p := by
    rw [hpform',T.chainSet_append,T.chainSet_append,T.chainSet_append,T.chainSet_append,holdset]
  have hc : T.count (l.append (old.append b))=T.count p := congrArg Finset.card hs
  have hd := T.distance_le_walk H (T.important_spec hst).1 (l.append (old.append b)) hall
  omega

/-- Every positive legal raw insertion newly saturates an actual important
pair in its own tail row; no candidate category is excluded. -/
theorem positive_choice_new_saturation {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {u v : V} (he : (u,v)∈candidates T.G)
    (hdrop : T.potential (insert (u,v) H)<T.potential H) :
    ∃ w,(u,w)∈T.unsaturated H ∧
      T.distance (insert (u,v) H) u w=T.endpointFloor u w := by
  classical
  by_cases hv : label T.chains v=none
  · obtain ⟨st,hst,hd⟩ := T.exists_improved_pair hdrop
    exact T.uncovered_improvement_new_saturation hH he hv hst hd
  · have hu := T.positive_covered_choice hH he hv hdrop
    exact ⟨v,hu,T.direct_important_candidate_saturated H he (Finset.mem_filter.mp hu).1⟩

end GreedyShortcuts.ChainDistance.Context
