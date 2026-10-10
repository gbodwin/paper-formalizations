import GreedyShortcuts.ChainInteriorSavings

/-! Actual multi-source, multi-target charging for an interior insertion.
These structural lemmas do not assert existence of a large rectangle. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- A rectangle counts each actual important pair once. No disjointness
between the source vertex set and the target vertex set is required. -/
theorem rectangle_drop_lower_bound (H : Finset (V × V)) (e : V × V)
    (sources targets : Finset V) (saving : ℕ)
    (hpairs : ∀ s ∈ sources,∀ t ∈ targets,(s,t) ∈ T.important)
    (hsave : ∀ s ∈ sources,∀ t ∈ targets,
      saving ≤ T.distance H s t-T.distance (insert e H) s t) :
    sources.card*targets.card*saving ≤ T.potential H-T.potential (insert e H) := by
  classical
  rw [T.potential_drop_sum]
  have hsub : sources ×ˢ targets ⊆ T.important := by
    intro st hst
    have h := Finset.mem_product.mp hst
    exact hpairs _ h.1 _ h.2
  calc
    sources.card*targets.card*saving = ∑ _st ∈ sources ×ˢ targets,saving := by simp
    _ ≤ ∑ st ∈ sources ×ˢ targets,
        (T.distance H st.1 st.2-T.distance (insert e H) st.1 st.2) := by
      apply Finset.sum_le_sum
      intro st hst
      have h := Finset.mem_product.mp hst
      exact hsave _ h.1 _ h.2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

/-- If the same interior segment occurs in actual minimum valid walks for
all pairs of a rectangle, one insertion earns all its savings. Each source
has its own unchanged filter and must admit the new endpoint as an entry. -/
theorem rectangle_insertion_drop {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {u v : V} (q : DWalk u v) (hne : u≠v) (sources targets : Finset V)
    (hpairs : ∀ s ∈ sources,∀ t ∈ targets,(s,t) ∈ T.important)
    (hentries : ∀ s ∈ sources,(s,v) ∈ T.important)
    (hpaths : ∀ s ∈ sources,∀ t ∈ targets,∃ (p : DWalk s u) (r : DWalk v t),
      Allowed (T.graph H s) ((p.append q).append r) ∧
      T.count ((p.append q).append r) = T.distance H s t) :
    sources.card*targets.card*(T.count q-2) ≤
      T.potential H-T.potential (insert (u,v) H) := by
  apply T.rectangle_drop_lower_bound H (u,v) sources targets (T.count q-2) hpairs
  intro s hs t ht
  obtain ⟨p,r,hall,hmin⟩ := hpaths s hs t ht
  exact T.interior_insertion_drop hH p q r hall hmin (hentries s hs) hne

end GreedyShortcuts.ChainDistance.Context
