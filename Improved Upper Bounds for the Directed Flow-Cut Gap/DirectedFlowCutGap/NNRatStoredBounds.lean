import DirectedFlowCutGap.RawNonnegativeRational

/-!
# Stored widths of canonical nonnegative rationals

Reduction of a represented fraction can only shrink its numerator and
denominator. This transfers the existing raw arithmetic width bounds
to the canonical values used as inputs to subsequent adaptive calls.
-/

namespace DirectedFlowCutGap.NNRatStoredBounds

open scoped NNRat BigOperators
open RawNonnegativeRational

abbrev Bounded (q : ℚ≥0) (B : ℕ) : Prop := (Code.ofNNRat q).Bounded B

theorem canonical_le (q : Code) : q.value.num ≤ q.num ∧ q.value.den ≤ q.den := by
  have he : (q.value : ℚ) = Rat.divInt (q.num : ℤ) (q.den : ℤ) := by
    simp only [Rat.divInt_eq_div, Code.value, NNRat.coe_div, NNRat.coe_natCast,
      Int.cast_natCast]
  have hd : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.positive_den.ne'
  constructor
  · by_cases hn : q.num = 0
    · rw [(Code.value_eq_zero q).mpr hn, NNRat.num_zero, hn]
    · change ((q.value : ℚ).num.natAbs) ≤ q.num
      rw [he]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Int.ofNat_dvd_right.mp (Rat.num_dvd _ hd))
  · change (q.value : ℚ).den ≤ q.den
    rw [he]
    exact Nat.le_of_dvd q.positive_den (Int.ofNat_dvd.mp (Rat.den_dvd _ _))

theorem value_bounded {q : Code} {B : ℕ} (h : q.Bounded B) : Bounded q.value B := by
  have hc := canonical_le q
  exact ⟨hc.1.trans h.1, hc.2.trans h.2⟩

theorem zero_bounded : Bounded 0 0 := Code.bounded_zero
theorem one_bounded : Bounded 1 0 := Code.bounded_one

theorem mono {q : ℚ≥0} {a b : ℕ} (h : Bounded q a) (hab : a ≤ b) : Bounded q b :=
  Code.bounded_mono h hab

theorem add_bounded {x y : ℚ≥0} {a b : ℕ} (hx : Bounded x a) (hy : Bounded y b) :
    Bounded (x + y) (a+b+1) := by
  simpa only [Code.value_add, Code.value_ofNNRat] using value_bounded (Code.bounded_add hx hy)

theorem mul_bounded {x y : ℚ≥0} {a b : ℕ} (hx : Bounded x a) (hy : Bounded y b) :
    Bounded (x * y) (a+b) := by
  simpa only [Code.value_mul, Code.value_ofNNRat] using value_bounded (Code.bounded_mul hx hy)

theorem div_bounded {x y : ℚ≥0} {a b : ℕ} (hx : Bounded x a) (hy : Bounded y b) :
    Bounded (x / y) (a+b) := by
  simpa only [Code.value_div, Code.value_ofNNRat] using value_bounded (Code.bounded_div hx hy)

theorem max_bounded {x y : ℚ≥0} {B : ℕ} (hx : Bounded x B) (hy : Bounded y B) :
    Bounded (max x y) B := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]; exact hy
  · rw [max_eq_left h]; exact hx

theorem pow_bounded {x : ℚ≥0} {B : ℕ} (hx : Bounded x B) (k : ℕ) :
    Bounded (x ^ k) (B*k) := by
  constructor
  · change (x ^ k).num ≤ 2 ^ (B*k)
    rw [NNRat.num_pow, pow_mul]
    exact Nat.pow_le_pow_left hx.1 _
  · change (x ^ k).den ≤ 2 ^ (B*k)
    rw [NNRat.den_pow, pow_mul]
    exact Nat.pow_le_pow_left hx.2 _

theorem sum_bounded {E : Type} (S : Finset E) (q : E → ℚ≥0) (B : ℕ)
    (h : ∀ e ∈ S, Bounded (q e) B) : Bounded (∑ e ∈ S, q e) (S.card * (B + 1)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Finset.card_empty, Nat.zero_mul] using zero_bounded
  | @insert e S hn ih =>
    have hx := h e (Finset.mem_insert_self ..)
    have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    rw [Finset.card_insert_of_notMem hn, Finset.sum_insert hn]
    convert add_bounded hx hs using 1
    ring

end DirectedFlowCutGap.NNRatStoredBounds
