import Mathlib.Tactic

/-!
Finite, division-free potential decay. The graph-specific progress inequality
is an explicit hypothesis here, not an assumed theorem about shortcut sets.
Instantiating it for the actual greedy graph algorithm remains a separate task.
-/

namespace GreedyShortcuts.FinitePotential

/-- Relative integer progress halves a potential in one block of `D` steps.
This avoids analytic logarithms and any rounding of fractional decrements. -/
theorem half_in_block (P : ℕ → ℕ) (D : ℕ) (hD : 0 < D)
    (hmono : Antitone P)
    (hstep : ∀ i < D, P i ≤ D * (P i - P (i + 1))) :
    2 * P D ≤ P 0 := by
  have hsum : ∀ t, t ≤ D → D * P t + t * P D ≤ D * P 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      intro ht
      have htD : t < D := by omega
      have hi := ih (by omega)
      have hm : P D ≤ P t := hmono (by omega)
      have hn : P (t + 1) ≤ P t := hmono (Nat.le_succ t)
      have hd := hstep t htD
      have heq : P (t + 1) + (P t - P (t + 1)) = P t := Nat.add_sub_of_le hn
      have heqD := congrArg (fun x : ℕ => D * x) heq
      nlinarith
  have h := hsum D (le_refl _)
  have hm : D * (2 * P D) ≤ D * P 0 := by nlinarith
  exact Nat.le_of_mul_le_mul_left hm hD

/-- Iterating the block estimate gives an exact dyadic bound. -/
theorem dyadic_blocks (P : ℕ → ℕ) (D : ℕ) (hD : 0 < D)
    (hmono : Antitone P)
    (hstep : ∀ i, P i ≤ D * (P i - P (i + 1))) (k : ℕ) :
    2 ^ k * P (k * D) ≤ P 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hm : Antitone (fun i => P (k * D + i)) := by
      intro a b hab
      exact hmono (Nat.add_le_add_left hab _)
    have hs : ∀ i < D,
        P (k * D + i) ≤ D * (P (k * D + i) - P (k * D + (i + 1))) := by
      intro i _
      simpa only [Nat.add_assoc] using hstep (k * D + i)
    have hh := half_in_block (fun i => P (k * D + i)) D hD hm hs
    simp only [Nat.add_zero] at hh
    have hmul := Nat.mul_le_mul_left (2 ^ k) hh
    rw [pow_succ, Nat.succ_mul]
    nlinarith

/-- A natural potential below one must be zero. The exponent can later be
chosen as the bit length of the initial graph potential. -/
theorem zero_after_blocks (P : ℕ → ℕ) (D k : ℕ) (hD : 0 < D)
    (hmono : Antitone P)
    (hstep : ∀ i, P i ≤ D * (P i - P (i + 1)))
    (hsmall : P 0 < 2 ^ k) : P (k * D) = 0 := by
  have hb := dyadic_blocks P D hD hmono hstep k
  by_contra hne
  have hpos : 1 ≤ P (k * D) := Nat.one_le_iff_ne_zero.mpr hne
  have hmul := Nat.mul_le_mul_left (2 ^ k) hpos
  nlinarith

end GreedyShortcuts.FinitePotential
