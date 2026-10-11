import GreedyShortcuts.ChainNewSaturation

/-! The unchanged raw greedy strictly depletes the actual unsaturated demand
set at every active step. This gives its cardinality as a finite stopping and
output budget, without asserting that this budget is linear in graph order. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset DirectedPaths
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- Any positive legal insertion strictly reduces the finite unsaturated
important-demand set, including insertions with uncovered destinations. -/
theorem unsaturated_card_lt_of_positive {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {e : V × V} (he : e∈candidates T.G)
    (hdrop : T.potential (insert e H)<T.potential H) :
    (T.unsaturated (insert e H)).card<(T.unsaturated H).card := by
  classical
  obtain ⟨u,v⟩ := e
  obtain ⟨w,hold,hnew⟩ := T.positive_choice_new_saturation hH he hdrop
  have hnot : (u,w)∉T.unsaturated (insert (u,v) H) := by
    intro hh
    have hh' := (Finset.mem_filter.mp hh).2
    change T.endpointFloor u w<T.distance (insert (u,v) H) u w at hh'
    exact (Nat.ne_of_gt hh') hnew
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr
    ⟨T.unsaturated_antitone (Finset.subset_insert _ _),fun h => hnot (h.symm ▸ hold)⟩

/-- Exact raw-greedy accounting: each active step adds one real edge and
retires at least one actual important demand. The optimizer is unchanged. -/
theorem run_card_add_unsaturated_le (D : ℕ) (hD : 2 ≤ D) (n : ℕ) :
    ((T.algorithm D hD).run n).1.card+
      (T.unsaturated ((T.algorithm D hD).run n).1).card ≤ (T.unsaturated ∅).card := by
  let A := T.algorithm D hD
  change (A.run n).1.card+(T.unsaturated (A.run n).1).card ≤ _
  induction n with
  | zero => simp [FiniteThresholdGreedy.System.run]
  | succ n ih =>
    by_cases h : ¬A.stopped (A.run n).1
    · have hd := A.bestEdge_improves (A.run n) h
      have hu := T.unsaturated_card_lt_of_positive (A.run n).2
        (A.bestEdge (A.run n) h).2.1 hd
      have hc := A.step_card_of_bad (A.run n) h
      have hu' : (T.unsaturated (A.step (A.run n)).1).card<
          (T.unsaturated (A.run n).1).card := by
        simpa only [FiniteThresholdGreedy.System.step,dite_eq_left h] using hu
      rw [A.run_succ]
      omega
    · have hs : A.stopped (A.run n).1 := Classical.not_not.mp h
      rw [A.run_succ,A.step_of_stopped (A.run n) hs]
      exact ih

/-- The original separate stopping predicate holds by the initial number
of unsaturated demands; zero initial demand count is included. -/
theorem stopped_by_unsaturated_initial (D : ℕ) (hD : 2 ≤ D) :
    T.stopped D ((T.algorithm D hD).run (T.unsaturated ∅).card).1 := by
  let A := T.algorithm D hD
  by_contra h
  have hbad : ¬A.stopped (A.run (T.unsaturated ∅).card).1 := h
  have hinv := T.run_card_add_unsaturated_le D hD (T.unsaturated ∅).card
  have hc := A.run_card_of_bad (T.unsaturated ∅).card hbad
  have hd := A.bestEdge_improves (A.run (T.unsaturated ∅).card) hbad
  have hu := T.unsaturated_card_lt_of_positive (A.run (T.unsaturated ∅).card).2
    (A.bestEdge (A.run (T.unsaturated ∅).card) hbad).2.1 hd
  change (A.run (T.unsaturated ∅).card).1.card+
    (T.unsaturated (A.run (T.unsaturated ∅).card).1).card ≤ _ at hinv
  omega

/-- A demand-sensitive budget for the same canonical raw-greedy output.
It is at most n*I, but is not claimed to be O(n) in general. -/
theorem output_card_le_unsaturated_initial (D : ℕ) (hD : 2 ≤ D) :
    (T.output D hD).card ≤ (T.unsaturated ∅).card :=
  (T.algorithm D hD).final_card_of_stopped_at _ (T.stopped_by_unsaturated_initial D hD)

end GreedyShortcuts.ChainDistance.Context
