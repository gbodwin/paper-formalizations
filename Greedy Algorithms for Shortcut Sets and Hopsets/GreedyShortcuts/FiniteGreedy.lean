import GreedyShortcuts.FinitePotential

/-!
An actual finite greedy insertion algorithm for an abstract natural potential.
The graph-specific existence of an improving closure edge is an explicit
interface obligation. It is not asserted here for the paper's graph models.
-/

namespace GreedyShortcuts.FiniteGreedy

variable {α : Type*} [DecidableEq α]

structure System (α : Type*) [DecidableEq α] where
  candidates : Finset α
  potential : Finset α → ℕ
  progress : ∀ S, S ⊆ candidates → 0 < potential S →
    ∃ e ∈ candidates, potential (insert e S) < potential S

namespace System

variable (A : System α)

abbrev State := {S : Finset α // S ⊆ A.candidates}

/-- A genuine minimizing candidate, with arbitrary tie-breaking. -/
noncomputable def bestEdge (S : A.State) (h : 0 < A.potential S.1) :
    {e : α // e ∈ A.candidates ∧
      ∀ x ∈ A.candidates, A.potential (insert e S.1) ≤ A.potential (insert x S.1)} := by
  classical
  have hn : A.candidates.Nonempty := by
    obtain ⟨e, he, _⟩ := A.progress S.1 S.2 h
    exact ⟨e, he⟩
  have hex := Finset.exists_min_image A.candidates
    (fun e => A.potential (insert e S.1)) hn
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

noncomputable def step (S : A.State) : A.State :=
  if h : 0 < A.potential S.1 then
    ⟨insert (A.bestEdge S h).1 S.1,
      Finset.insert_subset (A.bestEdge S h).2.1 S.2⟩
  else S

theorem bestEdge_improves (S : A.State) (h : 0 < A.potential S.1) :
    A.potential (insert (A.bestEdge S h).1 S.1) < A.potential S.1 := by
  obtain ⟨e, he, hp⟩ := A.progress S.1 S.2 h
  exact ((A.bestEdge S h).2.2 e he).trans_lt hp

theorem bestEdge_fresh (S : A.State) (h : 0 < A.potential S.1) :
    (A.bestEdge S h).1 ∉ S.1 := by
  intro he
  have hp := A.bestEdge_improves S h
  simp [Finset.insert_eq_of_mem he] at hp

/-- Minimizing the new potential is exactly the needed greedy maximum-drop
property, even though the drop is represented as natural subtraction. -/
theorem bestEdge_max_drop (S : A.State) (h : 0 < A.potential S.1)
    (e : α) (he : e ∈ A.candidates) :
    A.potential S.1 - A.potential (insert e S.1) ≤
      A.potential S.1 - A.potential (insert (A.bestEdge S h).1 S.1) :=
  Nat.sub_le_sub_left ((A.bestEdge S h).2.2 e he) _

theorem step_of_zero (S : A.State) (h : A.potential S.1 = 0) : A.step S = S := by
  simp [step, h]

theorem step_potential_lt (S : A.State) (h : 0 < A.potential S.1) :
    A.potential (A.step S).1 < A.potential S.1 := by
  simpa only [step, dite_eq_left h] using A.bestEdge_improves S h

theorem step_potential_le (S : A.State) :
    A.potential (A.step S).1 ≤ A.potential S.1 := by
  by_cases h : 0 < A.potential S.1
  · exact (A.step_potential_lt S h).le
  · have hz : A.potential S.1 = 0 := by omega
    rw [A.step_of_zero S hz]

theorem step_card_of_pos (S : A.State) (h : 0 < A.potential S.1) :
    (A.step S).1.card = S.1.card + 1 := by
  simpa only [step, dite_eq_left h] using Finset.card_insert_of_notMem (A.bestEdge_fresh S h)

theorem subset_step (S : A.State) : S.1 ⊆ (A.step S).1 := by
  by_cases h : 0 < A.potential S.1
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
    by_cases h : 0 < A.potential (A.run n).1
    · rw [run_succ, A.step_card_of_pos (A.run n) h]
      omega
    · have hz : A.potential (A.run n).1 = 0 := by omega
      rw [run_succ, A.step_of_zero (A.run n) hz]
      omega

theorem run_card_of_pos (n : ℕ) (h : 0 < A.potential (A.run n).1) :
    (A.run n).1.card = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0 < A.potential (A.run n).1 :=
      h.trans_le (A.step_potential_le (A.run n))
    rw [run_succ, A.step_card_of_pos (A.run n) hn, ih hn]

/-- By the time every candidate could have been inserted, the actual greedy
run has zero potential. No potential-decay rate is needed for termination. -/
theorem run_terminates : A.potential (A.run A.candidates.card).1 = 0 := by
  by_contra hne
  have hp : 0 < A.potential (A.run A.candidates.card).1 := Nat.pos_of_ne_zero hne
  have hc := A.run_card_of_pos A.candidates.card hp
  have hn := A.step_card_of_pos (A.run A.candidates.card) hp
  have hb := A.run_card_le (A.candidates.card + 1)
  rw [run_succ] at hb
  omega

/-- Once potential is zero, the implemented run is stationary. -/
theorem run_stable (n : ℕ) (hzero : A.potential (A.run n).1 = 0) (t : ℕ) :
    A.run (n + t) = A.run n := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.add_succ, run_succ, ih, A.step_of_zero (A.run n) hzero]

/-- Any proved stopping time bounds the cardinality of the canonical final
output, even if that time exceeds the number of candidates. -/
theorem final_card_of_zero_at (n : ℕ) (hzero : A.potential (A.run n).1 = 0) :
    (A.run A.candidates.card).1.card ≤ n := by
  by_cases h : n ≤ A.candidates.card
  · have hs : A.run A.candidates.card = A.run n := by
      simpa only [Nat.add_sub_of_le h] using
        A.run_stable n hzero (A.candidates.card - n)
    rw [hs]
    exact A.run_card_le_steps n
  · exact (A.run_card_le _).trans (by omega)

/-- A relative-progress candidate need not be the edge actually selected:
the true greedy maximizer does at least as well and therefore inherits the
finite dyadic stopping bound. -/
theorem run_zero_of_relative_progress (D k : ℕ) (hD : 0 < D)
    (hrelative : ∀ S : A.State, 0 < A.potential S.1 →
      ∃ e ∈ A.candidates,
        A.potential S.1 ≤ D * (A.potential S.1 - A.potential (insert e S.1)))
    (hsmall : A.potential ∅ < 2 ^ k) :
    A.potential (A.run (k * D)).1 = 0 := by
  refine FinitePotential.zero_after_blocks
    (fun n => A.potential (A.run n).1) D k hD A.run_potential_antitone ?_ ?_
  · intro i
    by_cases hi : 0 < A.potential (A.run i).1
    · obtain ⟨e, he, hg⟩ := hrelative (A.run i) hi
      have hm := Nat.mul_le_mul_left D (A.bestEdge_max_drop (A.run i) hi e he)
      have hc := hg.trans hm
      simpa only [run_succ, step, dite_eq_left hi] using hc
    · have hz : A.potential (A.run i).1 = 0 := by omega
      rw [hz]
      exact Nat.zero_le _
  · simpa only [run_zero] using hsmall

/-- Size bound for the actual canonical greedy output under a graph-specific
relative-progress interface. -/
theorem final_card_of_relative_progress (D k : ℕ) (hD : 0 < D)
    (hrelative : ∀ S : A.State, 0 < A.potential S.1 →
      ∃ e ∈ A.candidates,
        A.potential S.1 ≤ D * (A.potential S.1 - A.potential (insert e S.1)))
    (hsmall : A.potential ∅ < 2 ^ k) :
    (A.run A.candidates.card).1.card ≤ k * D :=
  A.final_card_of_zero_at (k * D)
    (A.run_zero_of_relative_progress D k hD hrelative hsmall)

end System
end GreedyShortcuts.FiniteGreedy
