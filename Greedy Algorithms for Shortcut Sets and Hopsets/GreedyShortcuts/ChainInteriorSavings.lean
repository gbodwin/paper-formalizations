import GreedyShortcuts.ChainPrefixSavings

/-! Interior replacement in the unchanged source filter. The old middle
segment need not be optimal after rebasing its source. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- Any nontrivial segment of an allowed walk yields a legal closure edge. -/
theorem interior_candidate {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u v : V} (q : DWalk u v) (hq : Allowed (T.graph H s) q) (hne : u≠v) :
    (u,v) ∈ candidates T.G := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne,
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨q,allowed_mono (fun _ _ h => h.1) hq⟩⟩

/-- One legal edge replaces an interior segment of a minimum walk. Both
pivot corrections cancel because all comparisons retain the original source.
The endpoint entry condition is only imposed relative to that source. -/
theorem interior_insertion_saving {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u v t : V} (p : DWalk s u) (q : DWalk u v) (r : DWalk v t)
    (hall : Allowed (T.graph H s) ((p.append q).append r))
    (hmin : T.count ((p.append q).append r) = T.distance H s t)
    (hentry : (s,v) ∈ T.important) (hne : u≠v) :
    T.distance (insert (u,v) H) s t+T.count q ≤ T.distance H s t+2 := by
  classical
  have hparts := (allowed_append _ (p.append q) r).mp hall
  have hpq := (allowed_append _ p q).mp hparts.1
  have he := T.interior_candidate hH q hpq.2 hne
  have hnewLegal : insert (u,v) H ⊆ candidates T.G := Finset.insert_subset he hH
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
  have hpb := (allowed_append _ p b).mpr ⟨hp',hb⟩
  have hnew := (allowed_append _ (p.append b) r).mpr ⟨hpb,hr'⟩
  have hd := T.distance_le_walk _ hst ((p.append b).append r) hnew
  have ho1 := T.count_append_exact hH p q hparts.1
  have ho2 := T.count_append_exact hH (p.append q) r hall
  have hn1 := T.count_append_exact hnewLegal p b hpb
  have hn2 := T.count_append_exact hnewLegal (p.append b) r hnew
  omega

/-- The same saving in natural-subtraction form, measured in the original
important-pair distance rather than in a source-rebased auxiliary distance. -/
theorem interior_insertion_drop {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u v t : V} (p : DWalk s u) (q : DWalk u v) (r : DWalk v t)
    (hall : Allowed (T.graph H s) ((p.append q).append r))
    (hmin : T.count ((p.append q).append r) = T.distance H s t)
    (hentry : (s,v) ∈ T.important) (hne : u≠v) :
    T.count q-2 ≤ T.distance H s t-T.distance (insert (u,v) H) s t := by
  have h := T.interior_insertion_saving hH p q r hall hmin hentry hne
  omega

end GreedyShortcuts.ChainDistance.Context
