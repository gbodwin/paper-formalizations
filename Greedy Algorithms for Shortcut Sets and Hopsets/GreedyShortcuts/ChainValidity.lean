import GreedyShortcuts.ChainGreedy

/-! Normalized minimizers and Algorithm 2's output are actual simple,
chain-contiguous, earliest-entry paths in a reachability-preserving DAG. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths CanonicalSegments ChainUnion ChainFirst
open ChainNormalization NormalizedReachability NormalizedValidity ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem augmentation_legal {H : Finset (V × V)} (hH : H ⊆ candidates T.G) :
    T.base ∪ H ⊆ candidates T.G :=
  Finset.union_subset (union_subset T.chains T.witnesses) hH

theorem graph_acyclic {H : Finset (V × V)} (hH : H ⊆ candidates T.G) (s : V) :
    Acyclic (T.graph H s) := by
  intro v p hp
  exact acyclic_augment T.acyclic (T.augmentation_legal hH) v p
    (allowed_mono (fun _ _ h => h.1) hp)

/-- Directed acyclicity forces every allowed walk to be simple. -/
theorem allowed_isPath {G : V → V → Prop} (hG : Acyclic G) {s t : V}
    (p : DWalk s t) (hp : Allowed G p) : p.IsPath := by
  induction p with
  | nil => exact Walk.IsPath.nil
  | @cons s u t ha p ih =>
    have hh := (allowed_cons G ha p).mp hp
    apply (Walk.cons_isPath_iff ha p).mpr
    refine ⟨ih hh.2,?_⟩
    intro hs
    have hback : Reachable G u s := ⟨p.takeUntil s hs,allowed_subwalk hh.2 (p.isSubwalk_takeUntil hs)⟩
    exact ha.ne ((acyclic_iff_reachable_antisymm G).mp hG s u (reachable_edge hh.1) hback)

theorem graph_convex {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} {p : DWalk s t} (hp : Allowed (T.graph H s) p)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (hk : k ≤ p.length)
    (c : I) (hi : label T.chains (p.getVert i) = some c)
    (hk' : label T.chains (p.getVert k) = some c) :
    label T.chains (p.getVert j) = some c := by
  apply color_convex (acyclic_augment T.acyclic (T.augmentation_legal hH))
    (label T.chains) (first T.chains) ?_ (first_constant T.chains) hp hij hjk hk c hi hk'
  intro u v hr hc
  have hg := (reachable_augment_iff T.G _ (T.augmentation_legal hH) u v).mp hr
  exact reachable_augment T.G _ (first_spec T.chains T.disjoint u v hg hc).2.1

theorem distance_valid_minimizer {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (hr : Reachable T.G s t) :
    ∃ p : DWalk s t,Allowed (T.graph H s) p ∧ p.IsPath ∧
      T.count p = T.distance H s t ∧
      ∀ i j k,i ≤ j → j ≤ k → k ≤ p.length → ∀ c : I,
        label T.chains (p.getVert i) = some c → label T.chains (p.getVert k) = some c →
          label T.chains (p.getVert j) = some c := by
  obtain ⟨p,hp,he⟩ := T.distance_spec H hr
  exact ⟨p,hp,allowed_isPath (T.graph_acyclic hH s) p hp,he,
    fun _ _ _ hij hjk hk c hi hk' => T.graph_convex hH hp hij hjk hk c hi hk'⟩

end GreedyShortcuts.ChainDistance.Context
