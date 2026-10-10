import GreedyShortcuts.ChainPrefixSavings

/-! Constructed suffix entry family and exact one-source potential charging.
The resulting quadratic-shaped product is a proved partial ingredient; the
paper's extra source multiplicity and cubic progress remain open. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def suffixEntries {s u t : V} (p : DWalk s u) (q : DWalk u t) : Finset V :=
  T.pathEntries (p.append q) ∩ q.support.toFinset

/-- All whole-path entries are either in the prefix entry set or on the
suffix. The overlap at the pivot is harmless for this lower bound. -/
theorem suffixEntries_count {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u t : V} (p : DWalk s u) (q : DWalk u t)
    (hpq : Allowed (T.graph H s) (p.append q)) :
    T.count (p.append q) ≤ T.count p+(T.suffixEntries p q).card := by
  classical
  have hp := (allowed_append _ p q).mp hpq |>.1
  have hsub : T.pathEntries (p.append q) ⊆ T.pathEntries p ∪ T.suffixEntries p q := by
    intro v hv
    have hvwalk := (T.pathEntries_mem hH (p.append q) hpq hv).1
    by_cases hvp : v ∈ p.support
    · apply Finset.mem_union_left
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hv
      refine Finset.mem_image.mpr ⟨c,?_,rfl⟩
      exact (T.mem_chainSet p c).mpr
        ⟨entry T.chains s c,hvp,T.entry_label hH (p.append q) hpq hc⟩
    · apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨hv,List.mem_toFinset.mpr
        ((Walk.mem_support_append_iff p q).mp hvwalk |>.resolve_left hvp)⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simpa only [T.pathEntries_card hH (p.append q) hpq,T.pathEntries_card hH p hp] using hc

/-- Every constructed suffix target receives the same real saving from one
important prefix shortcut; each contributes once to the original raw sum. -/
theorem suffixEntries_drop {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u t : V} (p : DWalk s u) (q : DWalk u t)
    (hpq : Allowed (T.graph H s) (p.append q))
    (hmin : T.count (p.append q) = T.distance H s t)
    (hpair : (s,u) ∈ T.important) :
    (T.suffixEntries p q).card*(T.count p-2) ≤
      T.potential H-T.potential (insert (s,u) H) := by
  classical
  apply T.source_drop_lower_bound
  · intro v hv
    exact (T.pathEntries_mem hH (p.append q) hpq (Finset.mem_inter.mp hv).1).2
  · intro v hv
    have hvq : v ∈ q.support := List.mem_toFinset.mp (Finset.mem_inter.mp hv).2
    let a := q.takeUntil v hvq
    let b := q.dropUntil v hvq
    have he : (p.append a).append b = p.append q := by
      dsimp only [a,b]
      rw [← Walk.append_assoc,q.take_spec hvq]
    have hall : Allowed (T.graph H s) ((p.append a).append b) := by simpa only [he] using hpq
    have hcost : T.count ((p.append a).append b) = T.distance H s t := by simpa only [he] using hmin
    have hshort := T.minimum_prefix hH (p.append a) b hall hcost
    exact T.prefix_insertion_drop hH p a ((allowed_append _ _ _).mp hall).1 hshort hpair

/-- The actual one-source product bound contains no assumed progress or
hereditary source-rebasing premise. Selecting/charging enough distinct
sources for a cubic bound is still a separate mathematical obligation. -/
theorem one_source_product_drop {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u t : V} (p : DWalk s u) (q : DWalk u t)
    (hpq : Allowed (T.graph H s) (p.append q))
    (hmin : T.count (p.append q) = T.distance H s t)
    (hpair : (s,u) ∈ T.important) :
    (T.distance H s t-T.count p)*(T.count p-2) ≤
      T.potential H-T.potential (insert (s,u) H) := by
  have hcount := T.suffixEntries_count hH p q hpq
  have hle : T.distance H s t-T.count p ≤ (T.suffixEntries p q).card := by omega
  exact (Nat.mul_le_mul_right (T.count p-2) hle).trans
    (T.suffixEntries_drop hH p q hpq hmin hpair)

end GreedyShortcuts.ChainDistance.Context
