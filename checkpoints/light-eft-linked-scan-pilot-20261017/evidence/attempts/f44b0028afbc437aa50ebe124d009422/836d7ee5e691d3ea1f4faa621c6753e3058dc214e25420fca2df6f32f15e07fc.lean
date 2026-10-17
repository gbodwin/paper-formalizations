import LightEFTSpanners.NativeBlockRefinement
import Mathlib.Data.Fintype.Sets

namespace LightEFTSpanners.MultigraphCuts
open Finset SimpleGraph
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

/-- A finite, explicit termination measure for actual partition refinement. -/
noncomputable def relatedPairs (R : Setoid V) : Finset (V×V) :=
  univ.filter (fun p => R.r p.1 p.2)

theorem relatedPairs_subset {R S : Setoid V} (h : R≤S) : relatedPairs R⊆relatedPairs S := by
  intro p hp
  simpa [relatedPairs] using h ((mem_filter.mp hp).2)

theorem relatedPairs_card_lt {R S : Setoid V} (h : R<S) :
    (relatedPairs R).card<(relatedPairs S).card := by
  apply card_lt_card
  refine lt_of_le_of_ne (relatedPairs_subset h.le) ?_
  intro heq
  apply h.ne
  apply Setoid.ext
  intro u v
  have hm := congrArg (fun T : Finset (V×V) => (u,v)∈T) heq
  simpa [relatedPairs] using hm

/-- The refinement cannot increase the number of within-block ordered pairs. -/
theorem componentRefinement_measure_le (H : SimpleGraph V) (R : Setoid V) :
    (relatedPairs (componentRefinement H R)).card≤(relatedPairs R).card :=
  card_le_card (relatedPairs_subset (componentRefinement_le H R))

theorem componentRefinement_measure_lt (H : SimpleGraph V) (R : Setoid V)
    (h : componentRefinement H R≠R) :
    (relatedPairs (componentRefinement H R)).card<(relatedPairs R).card :=
  relatedPairs_card_lt (lt_of_le_of_ne (componentRefinement_le H R) h)

/-- Genuine finite colors whose current block contains more than one connected
component. The least such color implements the source proof's priority rule. -/
noncomputable def splitColors {k : ℕ} (H : Fin k → SimpleGraph V) (R : Setoid V) :
    Finset (Fin k) := univ.filter (fun c => componentRefinement (H c) R≠R)

noncomputable def refinementStep {k : ℕ} (H : Fin k → SimpleGraph V) (R : Setoid V) :
    Setoid V := if h : (splitColors H R).Nonempty then
      componentRefinement (H ((splitColors H R).min' h)) R else R

omit [Fintype V] in
theorem refinementStep_le {k : ℕ} (H : Fin k → SimpleGraph V) (R : Setoid V) :
    refinementStep H R≤R := by
  unfold refinementStep
  split
  · exact componentRefinement_le _ _
  · exact le_rfl

omit [Fintype V] in
theorem refinementStep_eq_iff {k : ℕ} (H : Fin k → SimpleGraph V) (R : Setoid V) :
    refinementStep H R=R ↔ ∀ c,componentRefinement (H c) R=R := by
  classical
  by_cases h : (splitColors H R).Nonempty
  · have hn : componentRefinement (H ((splitColors H R).min' h)) R≠R :=
      by
        have hm := min'_mem (splitColors H R) h
        simpa only [splitColors,mem_filter,mem_univ,true_and] using hm
    simp only [refinementStep,dite_eq_left h]
    constructor
    · exact fun he => False.elim (hn he)
    · exact fun hall => False.elim (hn (hall _))
  · have hall : ∀ c,componentRefinement (H c) R=R := by
      intro c
      by_contra hn
      exact h ⟨c,by simp [splitColors,hn]⟩
    exact ⟨fun _ => hall,fun _ => by simp [refinementStep,h]⟩

theorem refinementStep_measure_lt {k : ℕ} (H : Fin k → SimpleGraph V) (R : Setoid V)
    (h : refinementStep H R≠R) :
    (relatedPairs (refinementStep H R)).card<(relatedPairs R).card :=
  relatedPairs_card_lt (lt_of_le_of_ne (refinementStep_le H R) h)

omit [Fintype V] in
theorem least_split_color_prior_fixed {k : ℕ} (H : Fin k → SimpleGraph V) (R : Setoid V)
    (h : (splitColors H R).Nonempty) {c : Fin k}
    (hc : c<(splitColors H R).min' h) : componentRefinement (H c) R=R := by
  classical
  by_contra hn
  have hm : c∈splitColors H R := by simp [splitColors,hn]
  exact (not_lt_of_ge (min'_le _ _ hm)) hc
end LightEFTSpanners.MultigraphCuts
