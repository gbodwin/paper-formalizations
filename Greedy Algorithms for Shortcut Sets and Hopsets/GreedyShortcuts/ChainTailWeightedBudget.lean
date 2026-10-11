import GreedyShortcuts.ChainSaturationTermination

/-! Exact tail-weighted accounting for the unchanged raw optimizer. Weights
only measure its output; they do not change its choice or stopping rule. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset DirectedPaths
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- The newly saturated witness has the same literal source as the inserted
edge, so any fixed nonnegative source weight can be charged to its retirement. -/
theorem unsaturated_tail_weight_drop (weight : V → ℕ)
    {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {e : V × V} (he : e ∈ candidates T.G)
    (hdrop : T.potential (insert e H) < T.potential H) :
    (∑ st ∈ T.unsaturated (insert e H),weight st.1)+weight e.1 ≤
      ∑ st ∈ T.unsaturated H,weight st.1 := by
  classical
  obtain ⟨u,v⟩ := e
  obtain ⟨t,hold,hnew⟩ := T.positive_choice_new_saturation hH he hdrop
  have hnot : (u,t) ∉ T.unsaturated (insert (u,v) H) := by
    intro hh
    exact (Nat.ne_of_gt (Finset.mem_filter.mp hh).2) hnew
  have hsub : insert (u,t) (T.unsaturated (insert (u,v) H)) ⊆ T.unsaturated H :=
    Finset.insert_subset hold (T.unsaturated_antitone (Finset.subset_insert _ _))
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun st : V × V => weight st.1) (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_insert hnot] at hs
  simpa only [Prod.fst, Nat.add_comm] using hs

/-- Weighted output plus remaining weighted demands never exceeds the initial
weighted demand count. Each weight is fixed by its original source. -/
theorem run_tail_weight_add_unsaturated_le (D : ℕ) (hD : 2 ≤ D)
    (weight : V → ℕ) (n : ℕ) :
    (∑ e ∈ ((T.algorithm D hD).run n).1,weight e.1)+
      (∑ st ∈ T.unsaturated ((T.algorithm D hD).run n).1,weight st.1) ≤
      ∑ st ∈ T.unsaturated ∅,weight st.1 := by
  classical
  let A := T.algorithm D hD
  change (∑ e ∈ (A.run n).1,weight e.1)+
    (∑ st ∈ T.unsaturated (A.run n).1,weight st.1) ≤ _
  induction n with
  | zero => simp [FiniteThresholdGreedy.System.run]
  | succ n ih =>
    by_cases h : ¬A.stopped (A.run n).1
    · have hs := T.unsaturated_tail_weight_drop weight (A.run n).2
        (A.bestEdge (A.run n) h).2.1 (A.bestEdge_improves (A.run n) h)
      have hf := A.bestEdge_fresh (A.run n) h
      rw [A.run_succ]
      simp only [FiniteThresholdGreedy.System.step,dite_eq_left h]
      rw [Finset.sum_insert hf]
      omega
    · have hz : A.stopped (A.run n).1 := Classical.not_not.mp h
      rw [A.run_succ,A.step_of_stopped (A.run n) hz]
      exact ih

/-- This measures the same canonical output, with no weighted-greedy premise. -/
theorem output_tail_weight_le (D : ℕ) (hD : 2 ≤ D) (weight : V → ℕ) :
    (∑ e ∈ T.output D hD,weight e.1) ≤ ∑ st ∈ T.unsaturated ∅,weight st.1 := by
  have h := T.run_tail_weight_add_unsaturated_le D hD weight (candidates T.G).card
  change (∑ e ∈ T.output D hD,weight e.1)+_ ≤ _ at h
  omega

/-- Every chosen-source subset has its own exact initial-demand budget. -/
theorem output_source_subset_card_le (D : ℕ) (hD : 2 ≤ D) (S : Finset V) :
    ((T.output D hD).filter (fun e => e.1 ∈ S)).card ≤
      ((T.unsaturated ∅).filter (fun st => st.1 ∈ S)).card := by
  classical
  have h := T.output_tail_weight_le D hD (fun u => if u ∈ S then 1 else 0)
  simpa only [Finset.sum_boole, Nat.cast_id] using h

end GreedyShortcuts.ChainDistance.Context
