import GreedyShortcuts.CanonicalSegments

/-! Source-dependent earliest-entry filtering preserves reachability in a DAG
once every chain can be traversed internally. This supplies a nonemptiness
foundation for the chain-normalized path model, not the cubic progress lemma. -/
namespace GreedyShortcuts.NormalizedReachability

open Finset SimpleGraph DirectedPaths CanonicalSegments
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V]

noncomputable def ancestors (G : V → V → Prop) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => Reachable G u v)

theorem ancestor_card_lt {G : V → V → Prop} (hG : Acyclic G) {u v : V}
    (huv : Reachable G u v) (hne : u ≠ v) : (ancestors G u).card < (ancestors G v).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_,?_⟩
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,reachable_trans (Finset.mem_filter.mp hx).2 huv⟩
  · intro he
    have hv : v ∈ ancestors G v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,reachable_refl G v⟩
    rw [← he] at hv
    exact hne ((acyclic_iff_reachable_antisymm G).mp hG u v huv (Finset.mem_filter.mp hv).2)

theorem reachable_eq_or_predecessor {G : V → V → Prop} {s t : V} (hr : Reachable G s t) :
    s = t ∨ ∃ u,Reachable G s u ∧ G u t ∧ u ≠ t := by
  obtain ⟨p,hp⟩ := hr
  induction p using Walk.concatRec with
  | Hnil => exact Or.inl rfl
  | @Hconcat s u t p h ih =>
    rw [Walk.concat_eq_append] at hp
    have hh := (allowed_append G p (.cons h .nil)).mp hp
    exact Or.inr ⟨u,⟨p,hh.1⟩,((allowed_cons G h .nil).mp hh.2).1,by simpa using h⟩

/-- The endpoint rule allows all unchained vertices, the selected earliest
vertex of a chain, and movement wholly within a chain. -/
def filtered (G : V → V → Prop) (color : V → Option I) (first : V → V → V)
    (s u v : V) : Prop := G u v ∧ (color u = color v ∨ color v = none ∨ first s v = v)

theorem filtered_inside {G : V → V → Prop} (color : V → Option I) (first : V → V → V)
    (s : V) {u v : V} {p : DWalk u v} (hp : Allowed G p)
    (hc : ∀ d ∈ p.darts,color d.fst = color d.snd) :
    Allowed (filtered G color first s) p := fun d hd => ⟨hp d hd,Or.inl (hc d hd)⟩

/-- If `first` picks a reachable earliest chain point and chains have internal
walks, earliest-entry filtering loses no reachable pair. All such walks are
constructed; no normalized-distance finiteness assumption is made. -/
theorem reachable_filtered_iff {G : V → V → Prop} (hG : Acyclic G)
    (color : V → Option I) (first : V → V → V)
    (hfirst : ∀ s v,Reachable G s v → color v ≠ none →
      Reachable G s (first s v) ∧ Reachable G (first s v) v ∧ color (first s v) = color v)
    (hinside : ∀ u v,Reachable G u v → color u = color v → color v ≠ none →
      ∃ p : DWalk u v,Allowed G p ∧ ∀ d ∈ p.darts,color d.fst = color d.snd)
    (s t : V) : Reachable (filtered G color first s) s t ↔ Reachable G s t := by
  constructor
  · exact reachable_mono (fun _ _ h => h.1)
  · refine (measure (fun v => (ancestors G v).card)).wf.induction
      (C := fun v => Reachable G s v → Reachable (filtered G color first s) s v) t ?_
    intro v ih hr
    by_cases he : color v = none ∨ first s v = v
    · rcases reachable_eq_or_predecessor hr with rfl | ⟨u,hu,huv,hne⟩
      · exact reachable_refl _ _
      · have hu' := ih u (ancestor_card_lt hG (reachable_edge huv) hne) hu
        exact reachable_trans hu' (reachable_edge ⟨huv,Or.inr he⟩)
    · have hc : color v ≠ none := fun h => he (Or.inl h)
      have hfne : first s v ≠ v := fun h => he (Or.inr h)
      obtain ⟨hfs,hfv,hfc⟩ := hfirst s v hr hc
      have hf := ih (first s v) (ancestor_card_lt hG hfv hfne) hfs
      obtain ⟨p,hp,hpc⟩ := hinside (first s v) v hfv hfc hc
      exact reachable_trans hf ⟨p,filtered_inside color first s hp hpc⟩

end GreedyShortcuts.NormalizedReachability
