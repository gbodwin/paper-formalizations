import GreedyShortcuts.FinitePotential

/-!
Finite raw-potential greedy with an independent monotone stopping condition.
Algorithm 2 minimizes a raw sum that need not vanish at termination; replacing
its stopping condition by zero potential would change the algorithm.
-/

namespace GreedyShortcuts.FiniteThresholdGreedy

variable {α : Type*} [DecidableEq α]

structure System (α : Type*) [DecidableEq α] where
  candidates : Finset α
  potential : Finset α → ℕ
  stopped : Finset α → Prop
  stopped_mono : Monotone stopped
  progress : ∀ S, S ⊆ candidates → ¬ stopped S →
    ∃ e ∈ candidates, potential (insert e S) < potential S

namespace System

variable (A : System α)

abbrev State := {S : Finset α // S ⊆ A.candidates}

/-- A genuine minimizing candidate, with arbitrary tie-breaking. -/
noncomputable def bestEdge (S : A.State) (h : ¬ A.stopped S.1) :
    {e : α // e ∈ A.candidates ∧
      ∀ x ∈ A.candidates, A.potential (insert e S.1) ≤ A.potential (insert x S.1)} := by
  classical
  have hn : A.candidates.Nonempty := by
    obtain ⟨e, he, _⟩ := A.progress S.1 S.2 h
    exact ⟨e, he⟩
  have hex := Finset.exists_min_image A.candidates
    (fun e => A.potential (insert e S.1)) hn
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

noncomputable def step (S : A.State) : A.State := by
  classical
  exact if h : ¬ A.stopped S.1 then
    ⟨insert (A.bestEdge S h).1 S.1,
      Finset.insert_subset (A.bestEdge S h).2.1 S.2⟩
  else S

theorem bestEdge_improves (S : A.State) (h : ¬ A.stopped S.1) :
    A.potential (insert (A.bestEdge S h).1 S.1) < A.potential S.1 := by
  obtain ⟨e, he, hp⟩ := A.progress S.1 S.2 h
  exact ((A.bestEdge S h).2.2 e he).trans_lt hp

theorem bestEdge_fresh (S : A.State) (h : ¬ A.stopped S.1) :
    (A.bestEdge S h).1 ∉ S.1 := by
  intro he
  have hp := A.bestEdge_improves S h
  simp [Finset.insert_eq_of_mem he] at hp

/-- Minimizing the new potential is exactly the needed greedy maximum-drop
property, even though the drop is represented as natural subtraction. -/
theorem bestEdge_max_drop (S : A.State) (h : ¬ A.stopped S.1)
    (e : α) (he : e ∈ A.candidates) :
    A.potential S.1 - A.potential (insert e S.1) ≤
      A.potential S.1 - A.potential (insert (A.bestEdge S h).1 S.1) :=
  Nat.sub_le_sub_left ((A.bestEdge S h).2.2 e he) _

theorem step_of_stopped (S : A.State) (h : A.stopped S.1) : A.step S = S := by
  simp [step, h]

theorem step_potential_lt (S : A.State) (h : ¬ A.stopped S.1) :
    A.potential (A.step S).1 < A.potential S.1 := by
  simpa only [step, dite_eq_left h] using A.bestEdge_improves S h

theorem step_potential_le (S : A.State) :
    A.potential (A.step S).1 ≤ A.potential S.1 := by
  by_cases h : ¬ A.stopped S.1
  · exact (A.step_potential_lt S h).le
  · have hz : A.stopped S.1 := Classical.not_not.mp h
    rw [A.step_of_stopped S hz]

theorem step_card_of_bad (S : A.State) (h : ¬ A.stopped S.1) :
    (A.step S).1.card = S.1.card + 1 := by
  simpa only [step, dite_eq_left h] using Finset.card_insert_of_notMem (A.bestEdge_fresh S h)

theorem subset_step (S : A.State) : S.1 ⊆ (A.step S).1 := by
  by_cases h : ¬ A.stopped S.1
  · simpa only [step, dite_eq_left h] using
      (Finset.subset_insert (A.bestEdge S h).1 S.1)
  · simpa only [step, dite_eq_right h] using (Finset.Subset.refl S.1)

noncomputable def run : ℕ → A.State
  | 0 => ⟨∅, Finset.empty_subset _⟩
  | n + 1 => A.step (run n)

@[simp] theorem run_zero : (A.run 0).1 = ∅ := rfl

@[simp] theorem run_succ (n : ℕ) : A.run (n + 1) = A.step (A.run n) := rfl

theorem run_potential_antitone : Antitone (fun n => A.potential (A.run n).1) :=
  antitone_nat_of_succ_le fun n => A.step_potential_le (A.run n)

theorem run_card_le (n : ℕ) : (A.run n).1.card ≤ A.candidates.card :=
  Finset.card_le_card (A.run n).2

theorem run_card_le_steps (n : ℕ) : (A.run n).1.card ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases h : ¬ A.stopped (A.run n).1
    · rw [run_succ, A.step_card_of_bad (A.run n) h]
      omega
    · have hz : A.stopped (A.run n).1 := Classical.not_not.mp h
      rw [run_succ, A.step_of_stopped (A.run n) hz]
      omega

theorem run_card_of_bad (n : ℕ) (h : ¬ A.stopped (A.run n).1) :
    (A.run n).1.card = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : ¬ A.stopped (A.run n).1 :=
      fun hs => h (A.stopped_mono (A.subset_step (A.run n)) hs)
    rw [run_succ, A.step_card_of_bad (A.run n) hn, ih hn]

/-- Every genuinely bad step adds a fresh candidate, so the actual raw-sum
minimizer reaches the specified stopping condition after finitely many steps. -/
theorem run_terminates : A.stopped (A.run A.candidates.card).1 := by
  by_contra hbad
  have hc := A.run_card_of_bad A.candidates.card hbad
  have hn := A.step_card_of_bad (A.run A.candidates.card) hbad
  have hb := A.run_card_le (A.candidates.card + 1)
  rw [run_succ] at hb
  omega

/-- The implemented run is stationary after its stopping condition holds. -/
theorem run_stable (n : ℕ) (hzero : A.stopped (A.run n).1) (t : ℕ) :
    A.run (n + t) = A.run n := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.add_succ, run_succ, ih, A.step_of_stopped (A.run n) hzero]

/-- Any proved stopping time bounds the cardinality of the canonical final
output, even if that time exceeds the number of candidates. -/
theorem final_card_of_stopped_at (n : ℕ) (hzero : A.stopped (A.run n).1) :
    (A.run A.candidates.card).1.card ≤ n := by
  by_cases h : n ≤ A.candidates.card
  · have hs : A.run A.candidates.card = A.run n := by
      simpa only [Nat.add_sub_of_le h] using
        A.run_stable n hzero (A.candidates.card - n)
    rw [hs]
    exact A.run_card_le_steps n
  · exact (A.run_card_le _).trans (by omega)

end System
end GreedyShortcuts.FiniteThresholdGreedy
