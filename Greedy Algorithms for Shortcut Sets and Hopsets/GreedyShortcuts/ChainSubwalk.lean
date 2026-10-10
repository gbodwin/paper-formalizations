import GreedyShortcuts.ChainValidity

/-! Validity, unlike normalized optimality, is inherited by subwalks.
This proves the source-change step using actual earliest-entry selectors and
DAG reachability; it does not assert the false hereditary-optimality claim. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem first_inherits {s u b : V} (hsu : Reachable T.G s u) (hub : Reachable T.G u b)
    (hc : label T.chains b ≠ none) (hf : first T.chains s b = b) :
    first T.chains u b = b := by
  have hu := first_spec T.chains T.disjoint u b hub hc
  have hs := first_spec T.chains T.disjoint s (first T.chains u b)
    (reachable_trans hsu hu.1) (by rw [hu.2.2]; exact hc)
  have he := (first_constant T.chains s (first T.chains u b) b hu.2.2).trans hf
  rw [he] at hs
  exact (acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ hu.2.1 hs.2.1

/-- Rebase an actual filtered walk from an ancestor's entry convention to
its own start vertex. The converse rebasing direction is generally false. -/
theorem allowed_rebase {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u v : V} (hsu : Reachable T.G s u) (q : DWalk u v) (hq : Allowed (T.graph H s) q) :
    Allowed (T.graph H u) q := by
  classical
  have ha : Allowed (augment T.G (T.base ∪ H)) q := allowed_mono (fun _ _ h => h.1) hq
  intro d hd
  have hh := hq d hd
  refine ⟨hh.1,?_⟩
  rcases hh.2 with hc | hc | hf
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · by_cases hc : label T.chains d.snd = none
    · exact Or.inr (Or.inl hc)
    · apply Or.inr ∘ Or.inr
      apply T.first_inherits hsu ?_ hc hf
      have hm := q.dart_snd_mem_support_of_mem_darts hd
      apply (reachable_augment_iff T.G _ (T.augmentation_legal hH) u d.snd).mp
      exact ⟨q.takeUntil d.snd hm,allowed_subwalk ha (q.isSubwalk_takeUntil hm)⟩

theorem subwalk_valid {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t u v : V} {p : DWalk s t} {q : DWalk u v}
    (hp : Allowed (T.graph H s) p) (hqp : q.IsSubwalk p) : Allowed (T.graph H u) q := by
  have hq := allowed_subwalk hp hqp
  obtain ⟨l,r,heq⟩ := hqp
  subst p
  have hl := ((allowed_append _ l q).mp ((allowed_append _ _ r).mp hp).1).1
  apply T.allowed_rebase hH ?_ q hq
  apply (reachable_augment_iff T.G _ (T.augmentation_legal hH) s u).mp
  exact ⟨l,allowed_mono (fun _ _ h => h.1) hl⟩

end GreedyShortcuts.ChainDistance.Context
