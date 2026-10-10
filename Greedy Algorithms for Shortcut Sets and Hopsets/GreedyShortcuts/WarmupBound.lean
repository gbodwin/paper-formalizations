import GreedyShortcuts.WarmupUnweighted

/-! A more familiar finite warm-up bound, including the small-hopbound case. -/
namespace GreedyShortcuts.WarmupBound

open GraphGreedy WarmupUnweighted
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem square_le_multiplicity (β : ℕ) : β ^ 2 ≤ 16 * repairMultiplicity β := by
  have hmod := Nat.mod_lt β (by decide : 0 < 4)
  have hdiv := Nat.mod_add_div β 4
  have hβ : β ≤ 4 * (β / 4 + 1) := by omega
  have hh := Nat.mul_self_le_mul_self hβ
  dsimp [repairMultiplicity]
  nlinarith

theorem blockLength_le (n β : ℕ) (hβ : 0 < β) :
    blockLength n β ≤ 16 * n ^ 2 / β ^ 2 + 1 := by
  have hr : 0 < repairMultiplicity β := by unfold repairMultiplicity; positivity
  have hq := Nat.div_mul_le_self (n ^ 2) (repairMultiplicity β)
  have hs := Nat.mul_le_mul_left (n ^ 2 / repairMultiplicity β) (square_le_multiplicity β)
  have hb : (n ^ 2 / repairMultiplicity β) * β ^ 2 ≤ 16 * n ^ 2 := by
    nlinarith
  have hd := (Nat.le_div_iff_mul_le (show 0 < β ^ 2 by positivity)).mpr hb
  exact Nat.add_le_add_right hd 1

/-- The actual greedy output obeys the familiar rounded warm-up bound,
for every positive integer hop target. -/
theorem output_card_bound_all (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β) :
    (output G β hβ).card ≤
      (Nat.log 2 ((Fintype.card V) ^ 3) + 1) * (16 * (Fintype.card V) ^ 2 / β ^ 2 + 1) := by
  by_cases hlarge : 4 ≤ β
  · exact (WarmupUnweighted.output_card_bound G β hlarge).trans
      (Nat.mul_le_mul_left _ (blockLength_le _ _ (by omega)))
  · have hs : β ^ 2 ≤ 16 := by nlinarith
    have hm := Nat.mul_le_mul_left ((Fintype.card V) ^ 2) hs
    have hdiv : (Fintype.card V) ^ 2 ≤ 16 * (Fintype.card V) ^ 2 / β ^ 2 := by
      apply (Nat.le_div_iff_mul_le (show 0 < β ^ 2 by positivity)).mpr
      simpa [Nat.mul_comm] using hm
    calc
      (output G β hβ).card ≤ (Fintype.card V) ^ 2 := output_card_le G β hβ
      _ ≤ 16 * (Fintype.card V) ^ 2 / β ^ 2 + 1 := by omega
      _ ≤ (Nat.log 2 ((Fintype.card V) ^ 3) + 1) *
          (16 * (Fintype.card V) ^ 2 / β ^ 2 + 1) := by
        exact Nat.le_mul_of_pos_left _ (by omega)

end GreedyShortcuts.WarmupBound
