import GreedyShortcuts.ChainEntryLevels
import GreedyShortcuts.ChainInteriorSavings

/-! Costs of routes through one inserted edge, without any assertion that
an original source-rebased subpath was minimum. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem important_inherits {s u v : V} (hentry : (s,v) ∈ T.important)
    (hsu : Reachable T.G s u) (huv : Reachable T.G u v) :
    (u,v) ∈ T.important := by
  obtain ⟨c,hvc⟩ := T.important_covered hentry
  have hf := T.first_inherits hsu huv (by simp [hvc]) (T.important_spec hentry).2
  simpa only [hf] using T.first_important huv hvc

/-- A covered start pivot and an important end pivot pay both joining
corrections. Neither the old walk nor its middle segment must be minimum. -/
theorem insertion_route_bound {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u v t : V} (p : DWalk s u) (q : DWalk u v) (r : DWalk v t)
    (hall : Allowed (T.graph H s) ((p.append q).append r))
    (huc : label T.chains u ≠ none) (hentry : (s,v) ∈ T.important) (hne : u≠v) :
    T.distance (insert (u,v) H) s t≤T.count p+T.count r := by
  classical
  have hparts := (allowed_append _ (p.append q) r).mp hall
  have hpq := (allowed_append _ p q).mp hparts.1
  have hst : Reachable T.G s t :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨(p.append q).append r,allowed_mono (fun _ _ h => h.1) hall⟩
  let b : DWalk u v := .cons (by simpa using hne) .nil
  have hb : Allowed (T.graph (insert (u,v) H) s) b := by
    change Allowed (T.graph (insert (u,v) H) s) (Walk.cons _ Walk.nil)
    rw [allowed_cons]
    refine ⟨⟨Or.inr ?_,Or.inr (Or.inr (T.important_spec hentry).2)⟩,allowed_nil _ _⟩
    exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  have hbc : T.count b≤2 := by simpa [b] using T.count_le_vertices b
  have hp' : Allowed (T.graph (insert (u,v) H) s) p :=
    allowed_mono (T.graph_mono (Finset.subset_insert _ _) s) hpq.1
  have hr' : Allowed (T.graph (insert (u,v) H) s) r :=
    allowed_mono (T.graph_mono (Finset.subset_insert _ _) s) hparts.2
  have hnew := (allowed_append _ (p.append b) r).mpr
    ⟨(allowed_append _ p b).mpr ⟨hp',hb⟩,hr'⟩
  have hd := T.distance_le_walk _ hst ((p.append b).append r) hnew
  obtain ⟨c,hc⟩ := Option.ne_none_iff_exists'.mp huc
  obtain ⟨d,hvc⟩ := T.important_covered hentry
  have h1 := T.count_append_covered p b hc
  have h2 := T.count_append_covered (p.append b) r hvc
  omega

omit [Fintype V] [DecidableEq V] in
/-- Splitting a prefix at two actual positions preserves the literal walk. -/
theorem take_append_segment {s t : V} (p : DWalk s t) {i j : ℕ} (hij : i≤j) :
    (p.take i).append (segment p i j hij)=p.take j := by
  have he : (p.take j).getVert i=p.getVert i := by
    rw [Walk.take_getVert,Nat.min_eq_right hij]
  have hprefix : ((p.take j).take i).copy rfl he=p.take i := by
    apply Walk.ext_support
    simp only [Walk.support_copy,Walk.support_take,List.take_take]
    congr 1
    omega
  have hh := Walk.append_copy_copy ((p.take j).take i) ((p.take j).drop i) rfl he rfl
  rw [hprefix,Walk.append_take_drop_eq,Walk.copy_rfl_rfl] at hh
  exact hh

/-- Exact cost of an interval, including its covered initial chain. -/
theorem count_segment_exact {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (p : DWalk s t) (hp : Allowed (T.graph H s) p)
    {i j : ℕ} (hij : i≤j) (hcovered : label T.chains (p.getVert i)≠none) :
    T.count (segment p i j hij)+T.count (p.take i)=T.count (p.take j)+1 := by
  classical
  have htake := allowed_subwalk hp (p.isSubwalk_take j)
  have hc := T.count_append_exact hH ((p.take j).take i) ((p.take j).drop i)
    (by simpa only [Walk.append_take_drop_eq] using htake)
  rw [Walk.append_take_drop_eq] at hc
  have hprefix : T.count ((p.take j).take i)=T.count (p.take i) := by
    unfold count
    rw [Walk.take_take,T.chainSet_copy,Nat.min_eq_right hij]
  obtain ⟨c,hc'⟩ := Option.ne_none_iff_exists'.mp hcovered
  have hlabel : label T.chains ((p.take j).getVert i)=some c := by
    simpa only [Walk.take_getVert,Nat.min_eq_right hij] using hc'
  have hs : T.count (segment p i j hij)=T.count ((p.take j).drop i) := by
    unfold count CanonicalSegments.segment
    rw [T.chainSet_copy]
  simp only [hlabel,Option.toFinset_some,Finset.card_singleton] at hc
  omega

end GreedyShortcuts.ChainDistance.Context
