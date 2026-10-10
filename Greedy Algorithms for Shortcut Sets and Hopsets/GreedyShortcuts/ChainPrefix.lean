import GreedyShortcuts.ChainCounting

/-! Exact splitting at a vertex and optimality of prefixes that retain the
original source. This does not assert optimality after source rebasing. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- A chain shared by the two parts of a valid path contains their joining
vertex. This is the exact consequence of chain contiguity needed for costs. -/
theorem chainSet_append_inter {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u t : V} (p : DWalk s u) (q : DWalk u t)
    (hpq : Allowed (T.graph H s) (p.append q)) :
    T.chainSet p ∩ T.chainSet q = (label T.chains u).toFinset := by
  classical
  ext c
  simp only [Finset.mem_inter,Option.mem_toFinset,Option.mem_def]
  constructor
  · rintro ⟨hp,hq⟩
    obtain ⟨a,ha,hac⟩ := (T.mem_chainSet p c).mp hp
    obtain ⟨b,hb,hbc⟩ := (T.mem_chainSet q c).mp hq
    obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.mp ha
    obtain ⟨j,hj,hjl⟩ := Walk.mem_support_iff_exists_getVert.mp hb
    have hi' : label T.chains ((p.append q).getVert i) = some c := by
      simpa only [Walk.getVert_append',if_pos hil,hi] using hac
    have hj' : label T.chains ((p.append q).getVert (p.length+j)) = some c := by
      simpa only [Walk.getVert_append,if_neg (by omega : ¬p.length+j<p.length),
        Nat.add_sub_cancel_left,hj] using hbc
    have hc := T.graph_convex hH hpq hil (by omega : p.length≤p.length+j)
      (by simpa only [Walk.length_append] using Nat.add_le_add_left hjl p.length) c hi' hj'
    simpa only [Walk.getVert_append,lt_self_iff_false,if_false,Nat.sub_self,Walk.getVert_zero] using hc
  · intro hc
    exact ⟨(T.mem_chainSet p c).mpr ⟨u,p.end_mem_support,hc⟩,
      (T.mem_chainSet q c).mpr ⟨u,q.start_mem_support,hc⟩⟩

/-- The shared joining chain is counted exactly once, including when the
joining vertex is uncovered and the correction is zero. -/
theorem count_append_exact {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u t : V} (p : DWalk s u) (q : DWalk u t)
    (hpq : Allowed (T.graph H s) (p.append q)) :
    T.count (p.append q)+(label T.chains u).toFinset.card = T.count p+T.count q := by
  unfold count
  rw [T.chainSet_append,← T.chainSet_append_inter hH p q hpq]
  exact Finset.card_union_add_card_inter _ _

/-- Prefixes of a minimum valid path are minimum for the unchanged source.
No claim is made about a subpath whose source has moved forward. -/
theorem minimum_prefix {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u t : V} (p : DWalk s u) (q : DWalk u t)
    (hpq : Allowed (T.graph H s) (p.append q))
    (hmin : T.count (p.append q) = T.distance H s t) :
    T.count p = T.distance H s u := by
  have hparts := (allowed_append _ p q).mp hpq
  have hsu : Reachable T.G s u :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨p,allowed_mono (fun _ _ h => h.1) hparts.1⟩
  have hst : Reachable T.G s t :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨p.append q,allowed_mono (fun _ _ h => h.1) hpq⟩
  obtain ⟨r,hr,hrc⟩ := T.distance_spec H hsu
  have hrep := (allowed_append _ r q).mpr ⟨hr,hparts.2⟩
  have hd := T.distance_le_walk H hst (r.append q) hrep
  have hpcount := T.count_append_exact hH p q hpq
  have hrcount := T.count_append_exact hH r q hrep
  have hle := T.distance_le_walk H hsu p hparts.1
  omega

end GreedyShortcuts.ChainDistance.Context
