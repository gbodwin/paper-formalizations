import Mathlib

/-!
# Finite dyadic labels for the edge-to-vertex reduction

Arithmetic for Theorem 30 of arXiv:2604.03412v3. The labels are zero and
`1, 1/2, ..., 1/2^(floor(log₂ n)+1)`. For positive `n`, weights at most
`1/(2n)` are dropped, weights at least one are clipped to one, and the
remaining weights are rounded upward. The extra bottom bin makes the
construction valid for every `n`, without assuming that `n` is a power of two.

The upper bound is always twice the input weight. Domination of the raw
input is claimed only below one: clipping heavy edges preserves the
threshold-one property, not their full weight. The empty case is explicitly
assigned the zero label. This file makes no claim about running time.
-/

namespace DirectedFlowCutGap.DyadicEdgeWeights
noncomputable section
open scoped NNReal

/-- A dyadic label value, with exponent zero representing one. -/
def dyadic (k : ℕ) : ℝ≥0 := (1 / 2) ^ k

@[simp] theorem dyadic_zero : dyadic 0 = 1 := by simp [dyadic]

theorem dyadic_pos (k : ℕ) : 0 < dyadic k := by
  dsimp [dyadic]
  positivity

theorem dyadic_le_one (k : ℕ) : dyadic k ≤ 1 :=
  pow_le_one₀ (by positivity) (by norm_num)

theorem dyadic_eq_one_div (k : ℕ) : dyadic k = 1 / (2 : ℝ≥0) ^ k := by
  simp [dyadic]

theorem dyadic_succ (k : ℕ) : dyadic (k + 1) * 2 = dyadic k := by
  dsimp [dyadic]
  rw [pow_succ]
  ring

theorem dyadic_antitone : Antitone dyadic := by
  intro i j hij
  rw [dyadic_eq_one_div, dyadic_eq_one_div]
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) hij)

/-- Search a finite sequence of dyadic values from its bottom upwards. -/
def ceilIndex : ℕ → ℝ≥0 → ℕ
  | 0, _ => 0
  | k + 1, w => if w ≤ dyadic (k + 1) then k + 1 else ceilIndex k w

theorem ceilIndex_le (k : ℕ) (w : ℝ≥0) : ceilIndex k w ≤ k := by
  induction k with
  | zero => simp [ceilIndex]
  | succ k ih =>
    simp only [ceilIndex]
    split_ifs
    · exact le_rfl
    · exact ih.trans (Nat.le_succ k)

theorem le_dyadic_ceilIndex (k : ℕ) {w : ℝ≥0} (hw : w ≤ 1) :
    w ≤ dyadic (ceilIndex k w) := by
  induction k with
  | zero => simpa [ceilIndex] using hw
  | succ k ih =>
    simp only [ceilIndex]
    split_ifs with h
    · exact h
    · exact ih

/-- The chosen exponent is maximal among eligible exponents. -/
theorem le_ceilIndex_of_le_dyadic (k : ℕ) {w : ℝ≥0} {j : ℕ}
    (hj : j ≤ k) (hw : w ≤ dyadic j) : j ≤ ceilIndex k w := by
  induction k generalizing j with
  | zero => simpa [ceilIndex] using hj
  | succ k ih =>
    simp only [ceilIndex]
    split_ifs with h
    · exact hj
    · have hjne : j ≠ k + 1 := by
        intro he
        exact h (he ▸ hw)
      exact ih (by omega) hw

/-- The selected dyadic value is the smallest eligible value in the list. -/
theorem dyadic_ceilIndex_le_of_le_dyadic (k : ℕ) {w : ℝ≥0} {j : ℕ}
    (hj : j ≤ k) (hw : w ≤ dyadic j) : dyadic (ceilIndex k w) ≤ dyadic j :=
  dyadic_antitone (le_ceilIndex_of_le_dyadic k hj hw)

/-- At the lowest bin a factor-two lower bound is enough; no logarithm of
an arbitrary real weight is needed. -/
theorem dyadic_ceilIndex_le_twice (k : ℕ) {w : ℝ≥0}
    (hb : dyadic k ≤ 2 * w) : dyadic (ceilIndex k w) ≤ 2 * w := by
  induction k with
  | zero => simpa [ceilIndex] using hb
  | succ k ih =>
    simp only [ceilIndex]
    split_ifs with h
    · exact hb
    · apply ih
      have hh := dyadic_succ k
      have hw : dyadic (k + 1) < w := lt_of_not_ge h
      nlinarith

/-- The largest positive-label exponent. -/
def depth (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- Zero is represented by `none`; `some i` represents `2^(-i)`. -/
abbrev Label (n : ℕ) := Option (Fin (depth n + 1))

/-- The nonnegative weight carried by a label. -/
def value (n : ℕ) : Label n → ℝ≥0
  | none => 0
  | some i => dyadic i.val

@[simp] theorem value_none (n : ℕ) : value n none = 0 := rfl
@[simp] theorem value_some (n : ℕ) (i : Fin (depth n + 1)) :
    value n (some i) = dyadic i.val := rfl

@[simp] theorem card_label (n : ℕ) : Fintype.card (Label n) = Nat.log 2 n + 3 := by
  simp [Label, depth, Nat.add_assoc]

theorem card_label_log2 (n : ℕ) : Fintype.card (Label n) = Nat.log2 n + 3 := by
  rw [Nat.log2_eq_log_two, card_label]

theorem value_le_one (n : ℕ) (i : Label n) : value n i ≤ 1 := by
  cases i with
  | none => exact zero_le
  | some i => exact dyadic_le_one i.val

/-- The original small-edge threshold; its value at zero is harmless. -/
def cutoff (n : ℕ) : ℝ≥0 := 1 / (2 * (n : ℝ≥0))

theorem cutoff_pos {n : ℕ} (hn : 0 < n) : 0 < cutoff n := by
  have h : (0 : ℝ≥0) < n := by exact_mod_cast hn
  dsimp [cutoff]
  positivity

theorem cutoff_le_half {n : ℕ} (hn : 0 < n) : cutoff n ≤ 1 / 2 := by
  have h : (1 : ℝ≥0) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
  dsimp [cutoff]
  exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)

theorem cutoff_lt_one {n : ℕ} (hn : 0 < n) : cutoff n < 1 :=
  (cutoff_le_half hn).trans_lt (by norm_num)

/-- Every positive label is at least the light-edge cutoff. -/
theorem cutoff_le_dyadic_depth {n : ℕ} (hn : 0 < n) :
    cutoff n ≤ dyadic (depth n) := by
  have hp : (2 : ℝ≥0) ^ Nat.log 2 n ≤ n := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
  rw [dyadic_eq_one_div]
  apply one_div_le_one_div_of_le (by positivity)
  dsimp [depth]
  rw [pow_succ]
  nlinarith

/-- The bottom dyadic label is at most twice the light-edge cutoff. -/
theorem dyadic_depth_le_twice_cutoff {n : ℕ} (hn : 0 < n) :
    dyadic (depth n) ≤ 2 * cutoff n := by
  have hn' : (0 : ℝ≥0) < n := by exact_mod_cast hn
  have hp : (n : ℝ≥0) ≤ (2 : ℝ≥0) ^ depth n := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
    exact_mod_cast h.le
  have he : 2 * cutoff n = 1 / (n : ℝ≥0) := by
    dsimp [cutoff]
    field_simp [ne_of_gt hn']
  rw [he, dyadic_eq_one_div]
  exact one_div_le_one_div_of_le hn' hp

theorem cutoff_le_value {n : ℕ} (hn : 0 < n) {i : Label n} (hi : i ≠ none) :
    cutoff n ≤ value n i := by
  cases i with
  | none => exact (hi rfl).elim
  | some i =>
    exact (cutoff_le_dyadic_depth hn).trans
      (dyadic_antitone (Nat.le_of_lt_succ i.isLt))

/-- The heavy-edge label. -/
def oneLabel (n : ℕ) : Label n := some ⟨0, by dsimp [depth]; omega⟩

@[simp] theorem value_oneLabel (n : ℕ) : value n (oneLabel n) = 1 := by
  simp [oneLabel, value]

/-- Actual finite rounding, including the empty-vertex case. -/
def round (n : ℕ) (w : ℝ≥0) : Label n :=
  if n = 0 then none else
  if w ≤ cutoff n then none else
  if 1 ≤ w then oneLabel n else
  some ⟨ceilIndex (depth n) w, Nat.lt_succ_of_le (ceilIndex_le _ _)⟩

@[simp] theorem round_zero_size (w : ℝ≥0) : round 0 w = none := by
  simp [round]

theorem round_of_le_cutoff (n : ℕ) {w : ℝ≥0} (hw : w ≤ cutoff n) :
    round n w = none := by
  by_cases hn : n = 0 <;> simp [round, hn, hw]

theorem round_of_one_le {n : ℕ} (hn : 0 < n) {w : ℝ≥0} (hw : 1 ≤ w) :
    round n w = oneLabel n := by
  have hl : ¬ w ≤ cutoff n := not_le.mpr ((cutoff_lt_one hn).trans_le hw)
  simp [round, Nat.ne_of_gt hn, hl, hw]

theorem value_round_of_one_le {n : ℕ} (hn : 0 < n) {w : ℝ≥0} (hw : 1 ≤ w) :
    value n (round n w) = 1 := by
  rw [round_of_one_le hn hw, value_oneLabel]

/-- A retained weight below one is dominated by its rounded value. -/
theorem le_value_round {n : ℕ} (hn : 0 < n) {w : ℝ≥0}
    (hl : cutoff n < w) (hw : w ≤ 1) : w ≤ value n (round n w) := by
  by_cases hh : 1 ≤ w
  · rw [value_round_of_one_le hn hh]
    exact hw
  · simp only [round, Nat.ne_of_gt hn, not_le.mpr hl, hh, ↓reduceIte, value_some]
    exact le_dyadic_ceilIndex (depth n) hw

/-- Rounding and clipping increase every input weight by at most two. -/
theorem value_round_le_twice (n : ℕ) (w : ℝ≥0) :
    value n (round n w) ≤ 2 * w := by
  by_cases hn : n = 0
  · subst n
    rw [round_zero_size, value_none]
    exact zero_le
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  by_cases hl : w ≤ cutoff n
  · rw [round_of_le_cutoff n hl, value_none]
    exact zero_le
  by_cases hh : 1 ≤ w
  · rw [value_round_of_one_le hn' hh]
    nlinarith
  · simp only [round, hn, hl, hh, ↓reduceIte, value_some]
    apply dyadic_ceilIndex_le_twice
    exact (dyadic_depth_le_twice_cutoff hn').trans
      (mul_le_mul_of_nonneg_left (le_of_not_ge hl) zero_le)

/-- Nonheavy edges lose only the additive small-edge threshold. This form
can be summed over at most `n` edges of an original simple path. -/
theorem le_value_round_add {n : ℕ} (hn : 0 < n) {w : ℝ≥0} (hw : w < 1) :
    w ≤ value n (round n w) + 1 / (2 * (n : ℝ≥0)) := by
  by_cases hl : w ≤ cutoff n
  · rw [round_of_le_cutoff n hl, value_none, zero_add]
    exact hl
  · exact (le_value_round hn (lt_of_not_ge hl) hw.le).trans (le_add_of_nonneg_right zero_le)

/-- A packaged intermediate-weight specification. -/
theorem intermediate_bounds {n : ℕ} (hn : 0 < n) {w : ℝ≥0}
    (hl : cutoff n < w) (hw : w < 1) :
    w ≤ value n (round n w) ∧ value n (round n w) ≤ 2 * w :=
  ⟨le_value_round hn hl hw.le, value_round_le_twice n w⟩

/-- All returned labels are capped at one, including heavy inputs. -/
theorem value_round_le_one (n : ℕ) (w : ℝ≥0) : value n (round n w) ≤ 1 :=
  value_le_one n (round n w)

end
end DirectedFlowCutGap.DyadicEdgeWeights
