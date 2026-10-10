import GreedyShortcuts.FiniteGreedy

/-! Bounded-horizon potential decay. The hopset analysis only promises
relative progress during the first input-edge-budget rounds. -/
namespace GreedyShortcuts.FiniteHorizon

open FiniteGreedy

theorem dyadic_blocks (P : ℕ → ℕ) (D k : ℕ) (hD : 0 < D)
    (hmono : Antitone P)
    (hstep : ∀ i < k * D, P i ≤ D * (P i - P (i + 1))) :
    2 ^ k * P (k * D) ≤ P 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hi := ih (fun i hi => hstep i (by rw [Nat.succ_mul]; omega))
    have hm : Antitone (fun i => P (k * D + i)) := by
      intro a b hab
      exact hmono (Nat.add_le_add_left hab _)
    have hs : ∀ i < D,
        P (k * D + i) ≤ D * (P (k * D + i) - P (k * D + (i + 1))) := by
      intro i hi
      have ht : k * D + i < (k + 1) * D := by rw [Nat.add_mul]; omega
      simpa only [Nat.add_assoc] using hstep (k * D + i) ht
    have hh := FinitePotential.half_in_block (fun i => P (k * D + i)) D hD hm hs
    simp only [Nat.add_zero] at hh
    have hmul := Nat.mul_le_mul_left (2 ^ k) hh
    rw [pow_succ, Nat.succ_mul]
    nlinarith

theorem zero_after_blocks (P : ℕ → ℕ) (D k : ℕ) (hD : 0 < D)
    (hmono : Antitone P)
    (hstep : ∀ i < k * D, P i ≤ D * (P i - P (i + 1)))
    (hsmall : P 0 < 2 ^ k) : P (k * D) = 0 := by
  have hb := dyadic_blocks P D k hD hmono hstep
  by_contra hne
  have hpos : 1 ≤ P (k * D) := Nat.one_le_iff_ne_zero.mpr hne
  have hm := Nat.mul_le_mul_left (2 ^ k) hpos
  nlinarith

variable {α : Type*} [DecidableEq α]

theorem run_zero_before (A : System α) (D k M : ℕ) (hD : 0 < D) (hbudget : k * D ≤ M)
    (hrelative : ∀ S : A.State, S.1.card < M → 0 < A.potential S.1 →
      ∃ e ∈ A.candidates,
        A.potential S.1 ≤ D * (A.potential S.1 - A.potential (insert e S.1)))
    (hsmall : A.potential ∅ < 2 ^ k) : A.potential (A.run (k * D)).1 = 0 := by
  apply zero_after_blocks (fun n => A.potential (A.run n).1) D k hD A.run_potential_antitone
  · intro i hi
    by_cases hp : 0 < A.potential (A.run i).1
    · obtain ⟨e, he, hg⟩ := hrelative (A.run i)
        ((A.run_card_le_steps i).trans_lt (hi.trans_le hbudget)) hp
      have hm := Nat.mul_le_mul_left D (A.bestEdge_max_drop (A.run i) hp e he)
      have hc := hg.trans hm
      simpa only [System.run_succ, System.step, dite_eq_left hp] using hc
    · have hz : A.potential (A.run i).1 = 0 := by omega
      rw [hz]
      exact Nat.zero_le _
  · simpa only [System.run_zero] using hsmall

theorem output_card_before (A : System α) (D k M : ℕ) (hD : 0 < D) (hbudget : k * D ≤ M)
    (hrelative : ∀ S : A.State, S.1.card < M → 0 < A.potential S.1 →
      ∃ e ∈ A.candidates,
        A.potential S.1 ≤ D * (A.potential S.1 - A.potential (insert e S.1)))
    (hsmall : A.potential ∅ < 2 ^ k) : (A.run A.candidates.card).1.card ≤ M :=
  (A.final_card_of_zero_at (k * D) (run_zero_before A D k M hD hbudget hrelative hsmall)).trans hbudget

end GreedyShortcuts.FiniteHorizon
