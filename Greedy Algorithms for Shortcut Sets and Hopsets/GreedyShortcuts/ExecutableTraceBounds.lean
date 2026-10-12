import GreedyShortcuts.FiniteExecutableGreedy
import GreedyShortcuts.FiniteThresholdDecay

/-! Tie-independent trace facts for the actual executable state sequence.
Only one-step potential values, not states or histories, are identified. -/
namespace GreedyShortcuts.FiniteExecutableGreedy.Represents
variable {α : Type*} [DecidableEq α] {A : FiniteThresholdGreedy.System α}
  {choices : List α} {score : Finset α → ℕ} {stopped : Finset α → Bool}
  (R : Represents A choices score stopped)
include R

theorem step_potential_eq (S : A.State) :
    A.potential (step choices score stopped S.1)=A.potential (A.step S).1 := by
  by_cases hs : A.stopped S.1
  · rw [R.step_of_stopped _ S.2 hs,A.step_of_stopped S hs]
  · obtain ⟨e,he,hstep,hm⟩ := R.step_minimizes S.1 S.2 hs
    rw [hstep]
    have hc : (A.step S).1=insert (A.bestEdge S hs).1 S.1 := by
      simp only [FiniteThresholdGreedy.System.step,dite_eq_left hs]
    rw [hc]
    exact Nat.le_antisymm (hm _ (A.bestEdge S hs).2.1) ((A.bestEdge S hs).2.2 e he)

theorem run_stable (k : ℕ) (hs : A.stopped (run choices score stopped k)) (j : ℕ) :
    run choices score stopped (k+j)=run choices score stopped k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ,run,ih,R.step_of_stopped _ (R.run_legal k) hs]

theorem run_card_le (k : ℕ) : (run choices score stopped k).card≤k := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    by_cases hs : A.stopped (run choices score stopped k)
    · rw [run,R.step_of_stopped _ (R.run_legal k) hs]
      omega
    · rw [run,R.step_card_active _ (R.run_legal k) hs]
      omega

theorem final_card_of_stopped_at (k : ℕ) (hs : A.stopped (run choices score stopped k)) :
    (run choices score stopped choices.toFinset.card).card≤k := by
  by_cases hk : choices.toFinset.card≤k
  · exact (R.run_card_le _).trans hk
  · have he : choices.toFinset.card=k+(choices.toFinset.card-k) := by omega
    rw [he,R.run_stable k hs]
    exact R.run_card_le k

end GreedyShortcuts.FiniteExecutableGreedy.Represents
