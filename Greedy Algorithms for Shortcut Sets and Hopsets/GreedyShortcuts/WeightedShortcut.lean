import GreedyShortcuts.WeightedMonotonicity

/-! Replace an actual shortest-path subwalk by its distance-closure edge.
The replacement preserves shortestness, rather than only reachability. -/
namespace GreedyShortcuts.WeightedPaths

open SimpleGraph DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking
open scoped NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem augment_insert_eq (G : V → V → Prop) (H : Finset (V × V)) (e : V × V) :
    augment (augment G H) {e} = augment G (insert e H) := by
  funext s t
  apply propext
  simp [augment, or_assoc, or_left_comm, or_comm]

theorem augmentWeight_insert_eq (G : V → V → Prop) (w : V → V → ℝ≥0)
    (H : Finset (V × V)) (hH : H ⊆ candidates G) (e : V × V) :
    augmentWeight (augment G H) (augmentWeight G w H) {e} =
      augmentWeight G w (insert e H) := by
  classical
  funext s t
  by_cases he : (s,t) = e
  · simp [augmentWeight, he, distance_augment G w H hH]
  · simp [augmentWeight, he]

/-- The replacement is a genuine shortest weighted walk. Its hop saving is
at least the removed subwalk length minus one. -/
theorem hop_after_subwalk {G : V → V → Prop} {w : V → V → ℝ≥0}
    {s t u v : V} {p : DWalk s t} {q : DWalk u v}
    (hp : Shortest G w p) (hq : q.IsSubwalk p) (huv : u ≠ v) :
    hopDistance (augment G {(u,v)}) (augmentWeight G w {(u,v)}) s t + q.length ≤ p.length + 1 := by
  have hqshort := hp.subwalk hq
  have hsingleton : {(u,v)} ⊆ candidates G := by
    apply Finset.singleton_subset_iff.mpr
    exact (mem_candidates G (u,v)).mpr ⟨huv, ⟨q, hqshort.1⟩⟩
  obtain ⟨l, r, rfl⟩ := hq
  have hh := (allowed_append G _ r).mp hp.1
  have hlq := (allowed_append G l q).mp hh.1
  have ha : (⊤ : SimpleGraph V).Adj u v := by simpa using huv
  let z : DWalk s t := (l.append (.cons ha .nil)).append r
  have hmono : ∀ a b, G a b → augment G {(u,v)} a b := fun _ _ => Or.inl
  have hz : Allowed (augment G {(u,v)}) z := by
    refine (allowed_append _ (l.append (.cons ha .nil)) r).mpr ⟨?_, allowed_mono hmono hh.2⟩
    refine (allowed_append _ l (.cons ha .nil)).mpr ⟨allowed_mono hmono hlq.1, ?_⟩
    simp [augment]
  have hcost : cost (augmentWeight G w {(u,v)}) z ≤ cost w ((l.append q).append r) := by
    have hl := cost_augment_le G w {(u,v)} l hlq.1
    have hr := cost_augment_le G w {(u,v)} r hh.2
    have heq := hqshort.cost_eq_distance
    simp only [z, cost_append, cost_cons, cost_nil, add_zero]
    rw [augmentWeight_of_mem G w (by simp : (u,v) ∈ ({(u,v)} : Finset (V × V))), ← heq]
    exact add_le_add (add_le_add hl (le_refl _)) hr
  have hzshort : Shortest (augment G {(u,v)}) (augmentWeight G w {(u,v)}) z := by
    refine ⟨hz, ?_⟩
    intro x hx
    calc
      cost (augmentWeight G w {(u,v)}) z ≤ cost w ((l.append q).append r) := hcost
      _ = (distance G w s t : ℝ) := hp.cost_eq_distance
      _ = (distance (augment G {(u,v)}) (augmentWeight G w {(u,v)}) s t : ℝ) := by
        rw [distance_augment G w _ hsingleton]
      _ ≤ cost (augmentWeight G w {(u,v)}) x := distance_le_cost _ _ x hx
  have hhop := hopDistance_le_of_shortest hzshort
  simp only [z, Walk.length_append, Walk.length_cons, Walk.length_nil] at hhop ⊢
  omega

/-- The same replacement applies to the exact insertion-sensitive state of
Algorithm 1, not only to an initially empty hopset. -/
theorem hop_after_subwalk_state {G : V → V → Prop} {w : V → V → ℝ≥0}
    {H : Finset (V × V)} (hH : H ⊆ candidates G)
    {s t u v : V} {p : DWalk s t} {q : DWalk u v}
    (hp : Shortest (augment G H) (augmentWeight G w H) p)
    (hq : q.IsSubwalk p) (huv : u ≠ v) :
    hopDistance (augment G (insert (u,v) H)) (augmentWeight G w (insert (u,v) H)) s t +
      q.length ≤ p.length + 1 := by
  have hh := hop_after_subwalk hp hq huv
  simpa only [augment_insert_eq, augmentWeight_insert_eq G w H hH] using hh

end GreedyShortcuts.WeightedPaths
