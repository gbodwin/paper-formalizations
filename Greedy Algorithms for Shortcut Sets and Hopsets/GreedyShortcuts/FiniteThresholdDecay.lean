import GreedyShortcuts.FiniteThresholdGreedy

/-! Quantitative stopping for the actual raw-potential minimizer. The clipped
sequence below is proof bookkeeping only; it does not change the algorithm. -/
namespace GreedyShortcuts.FiniteThresholdGreedy.System
variable {α : Type*} [DecidableEq α]
variable (A : FiniteThresholdGreedy.System α)

noncomputable def livePotential (n : ℕ) : ℕ := by
  classical
  exact if A.stopped (A.run n).1 then 0 else A.potential (A.run n).1

theorem livePotential_le (n : ℕ) : A.livePotential n ≤ A.potential (A.run n).1 := by
  classical
  unfold livePotential
  split_ifs <;> omega

theorem livePotential_antitone : Antitone A.livePotential := by
  classical
  apply antitone_nat_of_succ_le
  intro n
  by_cases hs : A.stopped (A.run n).1
  · have hn : A.stopped (A.run (n+1)).1 := by
      rw [run_succ,A.step_of_stopped _ hs]
      exact hs
    simp only [livePotential,ite_eq_left hs,ite_eq_left hn,Nat.le_refl]
  · have hl : A.livePotential n = A.potential (A.run n).1 := by
      simp only [livePotential,ite_eq_right hs]
    rw [hl]
    exact (A.livePotential_le (n+1)).trans (A.step_potential_le (A.run n))

/-- A relative rate for the unchanged raw greedy gives a finite stopping
time. Strict progress already ensures that nonstopped states have positive raw potential. -/
theorem stopped_after_relative_blocks (B k : ℕ) (hB : 0 < B)
    (hrate : ∀ S : A.State,¬ A.stopped S.1 →
      A.potential S.1 ≤ B*(A.potential S.1-A.potential (A.step S).1))
    (hsmall : A.potential ∅ < 2^k) : A.stopped (A.run (k*B)).1 := by
  classical
  have hstep : ∀ n,A.livePotential n ≤ B*(A.livePotential n-A.livePotential (n+1)) := by
    intro n
    by_cases hs : A.stopped (A.run n).1
    · simp only [livePotential,ite_eq_left hs,Nat.zero_le]
    · have hl : A.livePotential n=A.potential (A.run n).1 := by
        simp only [livePotential,ite_eq_right hs]
      rw [hl]
      exact (hrate (A.run n) hs).trans (Nat.mul_le_mul_left B
        (Nat.sub_le_sub_left (A.livePotential_le (n+1)) _))
  have hz := FinitePotential.zero_after_blocks A.livePotential B k hB
    A.livePotential_antitone hstep ((A.livePotential_le 0).trans_lt hsmall)
  by_contra hs
  have hp := A.step_potential_lt (A.run (k*B)) hs
  simp only [livePotential,ite_eq_right hs] at hz
  omega

theorem final_card_of_relative_blocks (B k : ℕ) (hB : 0 < B)
    (hrate : ∀ S : A.State,¬ A.stopped S.1 →
      A.potential S.1 ≤ B*(A.potential S.1-A.potential (A.step S).1))
    (hsmall : A.potential ∅ < 2^k) :
    (A.run A.candidates.card).1.card ≤ k*B :=
  A.final_card_of_stopped_at _ (A.stopped_after_relative_blocks B k hB hrate hsmall)

end GreedyShortcuts.FiniteThresholdGreedy.System
