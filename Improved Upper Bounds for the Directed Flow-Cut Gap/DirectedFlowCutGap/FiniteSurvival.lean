import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite sampling without replacement

The finite inequality used in printed Lemma 16 of arXiv:2604.03412v3 is proved
here, including its Maclaurin step. The proof balances two entries straddling
the mean, then inducts on the number of entries.

For a stopped epoch, the relevant event is the **joint** event that the epoch
reaches round `i` and the pair still survives. One can pre-sample a uniform
permutation and independent levels, and dominate that joint event by avoiding
every killing interval in the first `i` positions. Conditioning on the epoch
having survived can bias its first `i` choices. This file proves deterministic
finite inequalities; it does not assert that conditional uniformity or claim
to have formalized the measure-theoretic coupling to a stopped graph process.
-/

namespace DirectedFlowCutGap.FiniteSurvival

open scoped BigOperators

private theorem esymm_cons_succ (a : ℝ) (s : Multiset ℝ) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp [Multiset.esymm, Multiset.map_map,
    Multiset.sum_map_mul_left]

private theorem esymm_nonneg (s : Multiset ℝ) (h : ∀ x ∈ s, 0 ≤ x) (k : ℕ) :
    0 ≤ s.esymm k := by
  apply Multiset.sum_nonneg
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
  apply Multiset.prod_nonneg
  intro y hy
  exact h y (Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hy)

/-- Replacing a pair by another pair with the same sum and larger product
increases each elementary symmetric sum of nonnegative remaining entries. -/
private theorem esymm_pair_balance (s : Multiset ℝ)
    (hs : ∀ x ∈ s, 0 ≤ x) (a b c d : ℝ)
    (hsum : a + b = c + d) (hprod : a * b ≤ c * d) (k : ℕ) :
    (a ::ₘ b ::ₘ s).esymm k ≤ (c ::ₘ d ::ₘ s).esymm k := by
  rcases k with _ | _ | k
  · simp
  · simp only [esymm_cons_succ, Multiset.esymm_zero, mul_one]
    linarith
  · simp only [esymm_cons_succ]
    have hp := mul_le_mul_of_nonneg_right hprod (esymm_nonneg s hs k)
    have hsprod := congrArg (fun x : ℝ => x * s.esymm (k + 1)) hsum
    nlinarith

private theorem sum_le_card_mul (s : Multiset ℝ) (m : ℝ)
    (h : ∀ x ∈ s, x ≤ m) : s.sum ≤ (s.card : ℝ) * m := by
  simpa only [nsmul_eq_mul] using s.sum_le_card_nsmul m h

private theorem card_mul_le_sum (s : Multiset ℝ) (m : ℝ)
    (h : ∀ x ∈ s, m ≤ x) : (s.card : ℝ) * m ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [Multiset.card_cons, Multiset.sum_cons, Nat.cast_add, Nat.cast_one]
    linarith

private theorem esymm_cons_mean_bound (s : Multiset ℝ) (m : ℝ) (hm : 0 ≤ m)
    (h : ∀ k : ℕ, s.esymm k ≤ (s.card.choose k : ℝ) * m ^ k) (k : ℕ) :
    (m ::ₘ s).esymm k ≤ ((s.card + 1).choose k : ℝ) * m ^ k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [esymm_cons_succ]
    calc
      s.esymm (k + 1) + m * s.esymm k ≤
          (s.card.choose (k + 1) : ℝ) * m ^ (k + 1) +
            m * ((s.card.choose k : ℝ) * m ^ k) :=
        add_le_add (h _) (mul_le_mul_of_nonneg_left (h _) hm)
      _ = ((s.card + 1).choose (k + 1) : ℝ) * m ^ (k + 1) := by
        rw [Nat.choose_succ_succ', Nat.cast_add, pow_succ]
        ring

/-- Maclaurin's first-mean inequality, in unnormalized multiset form.
There are no distinctness assumptions on the numerical entries. -/
theorem esymm_le_choose_mul_pow_of_sum_eq (n : ℕ) (s : Multiset ℝ)
    (hcard : s.card = n) (m : ℝ) (hm : 0 ≤ m)
    (hs : ∀ x ∈ s, 0 ≤ x) (hsum : s.sum = (n : ℝ) * m) (k : ℕ) :
    s.esymm k ≤ (n.choose k : ℝ) * m ^ k := by
  classical
  induction n using Nat.strong_induction_on generalizing s m k with
  | h n ih =>
    by_cases hz : s = 0
    · subst s
      have hn : n = 0 := by simpa using hcard.symm
      subst n
      cases k <;> simp [Multiset.esymm, Multiset.powersetCard_zero_right]
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hz
    obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
    have htcard : t.card < n := by rw [← hcard]; simp
    have hn : n = t.card + 1 := by simpa using hcard.symm
    have ha0 : 0 ≤ a := hs a (by simp)
    have ht0 : ∀ x ∈ t, 0 ≤ x := fun x hx => hs x (by simp [hx])
    have hsum' : a + t.sum = ((t.card : ℝ) + 1) * m := by
      simpa [hn] using hsum
    have mean_bound : ∀ (u : Multiset ℝ), u.card = t.card →
        (∀ x ∈ u, 0 ≤ x) → u.sum = (t.card : ℝ) * m →
        ∀ j : ℕ, (m ::ₘ u).esymm j ≤ (n.choose j : ℝ) * m ^ j := by
      intro u hu hu0 husum j
      rw [hn, ← hu]
      apply esymm_cons_mean_bound u m hm
      intro l
      exact ih u.card (by simpa [hu] using htcard) u rfl m hm hu0 (by simpa [hu] using husum) l
    by_cases ham : a = m
    · subst a
      apply mean_bound t rfl ht0
      linarith
    have hb : ∃ b ∈ t, 0 ≤ a + b - m ∧ a * b ≤ m * (a + b - m) := by
      rcases lt_or_gt_of_ne ham with ham | hma
      · have hex : ∃ b ∈ t, m ≤ b := by
          by_contra hnone
          have hall : ∀ b ∈ t, b ≤ m := by
            intro b hb
            exact le_of_lt (lt_of_not_ge (fun hmb => hnone ⟨b, hb, hmb⟩))
          have hle := sum_le_card_mul t m hall
          linarith
        obtain ⟨b, hbt, hmb⟩ := hex
        refine ⟨b, hbt, by linarith, ?_⟩
        nlinarith [mul_nonneg (sub_nonneg.mpr ham.le) (sub_nonneg.mpr hmb)]
      · have hex : ∃ b ∈ t, b ≤ m := by
          by_contra hnone
          have hall : ∀ b ∈ t, m ≤ b := by
            intro b hb
            exact le_of_lt (lt_of_not_ge (fun hbm => hnone ⟨b, hb, hbm⟩))
          have hle := card_mul_le_sum t m hall
          linarith
        obtain ⟨b, hbt, hbm⟩ := hex
        refine ⟨b, hbt, by linarith [ht0 b hbt], ?_⟩
        nlinarith [mul_nonneg (sub_nonneg.mpr hma.le) (sub_nonneg.mpr hbm)]
    obtain ⟨b, hbt, hc0, hprod⟩ := hb
    obtain ⟨v, rfl⟩ := Multiset.exists_cons_of_mem hbt
    have hv0 : ∀ x ∈ v, 0 ≤ x := fun x hx => ht0 x (by simp [hx])
    calc
      (a ::ₘ b ::ₘ v).esymm k ≤ (m ::ₘ (a + b - m) ::ₘ v).esymm k :=
        esymm_pair_balance v hv0 a b m (a + b - m) (by ring) hprod k
      _ ≤ (n.choose k : ℝ) * m ^ k := by
        apply mean_bound ((a + b - m) ::ₘ v) (by simp)
        · intro x hx
          rcases Multiset.mem_cons.mp hx with rfl | hx
          · exact hc0
          · exact hv0 x hx
        · simp only [Multiset.sum_cons, Multiset.card_cons, Nat.cast_add,
            Nat.cast_one] at hsum' ⊢
          linarith

/-- The arithmetic mean of a function over all `k`-element subsets of `s`.
The denominator is exactly the cardinality of `s.powersetCard k`. -/
noncomputable def subsetAverage {E : Type*} (s : Finset E) (k : ℕ)
    (f : Finset E → ℝ) : ℝ :=
  (∑ t ∈ s.powersetCard k, f t) / (s.card.choose k : ℝ)

/-- Exact identification of the normalization with the uniform finite average. -/
theorem subsetAverage_eq_card_average {E : Type*} (s : Finset E) (k : ℕ)
    (f : Finset E → ℝ) :
    subsetAverage s k f =
      (∑ t ∈ s.powersetCard k, f t) / ((s.powersetCard k).card : ℝ) := by
  simp [subsetAverage]

/-- Maclaurin's inequality for the uniform average over fixed-size subsets. -/
theorem subset_product_average_le_mean_pow {E : Type*} (s : Finset E)
    (a : E → ℝ) (hs : 0 < s.card) (ha : ∀ e ∈ s, 0 ≤ a e)
    (k : ℕ) (hk : k ≤ s.card) :
    subsetAverage s k (fun t => ∏ e ∈ t, a e) ≤
      ((∑ e ∈ s, a e) / (s.card : ℝ)) ^ k := by
  classical
  have hN : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hC : (0 : ℝ) < s.card.choose k := by exact_mod_cast Nat.choose_pos hk
  have hm : 0 ≤ (∑ e ∈ s, a e) / (s.card : ℝ) :=
    div_nonneg (Finset.sum_nonneg ha) hN.le
  have he := esymm_le_choose_mul_pow_of_sum_eq s.card (s.val.map a)
    (by simp) ((∑ e ∈ s, a e) / (s.card : ℝ)) hm (by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp hx
      exact ha e he) (by
      simp only [Finset.sum_map_val]
      field_simp [hN.ne']) k
  rw [Finset.esymm_map_val] at he
  exact (div_le_iff₀ hC).mpr (by simpa [mul_comm] using he)

/-- The power of the mean has the required exponential decay.
Only nonnegativity is necessary; the intended application has `a e ≤ 1`. -/
theorem mean_pow_le_exp_neg_sum_complement {E : Type*} (s : Finset E)
    (a : E → ℝ) (hs : 0 < s.card) (ha : ∀ e ∈ s, 0 ≤ a e) (k : ℕ) :
    ((∑ e ∈ s, a e) / (s.card : ℝ)) ^ k ≤
      Real.exp (-(k : ℝ) * (∑ e ∈ s, (1 - a e)) / (s.card : ℝ)) := by
  have hN : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hm : 0 ≤ (∑ e ∈ s, a e) / (s.card : ℝ) :=
    div_nonneg (Finset.sum_nonneg ha) hN.le
  have hbase : (∑ e ∈ s, a e) / (s.card : ℝ) ≤
      Real.exp ((∑ e ∈ s, a e) / (s.card : ℝ) - 1) := by
    simpa using Real.add_one_le_exp ((∑ e ∈ s, a e) / (s.card : ℝ) - 1)
  calc
    ((∑ e ∈ s, a e) / (s.card : ℝ)) ^ k ≤
        (Real.exp ((∑ e ∈ s, a e) / (s.card : ℝ) - 1)) ^ k :=
      pow_le_pow_left₀ hm hbase k
    _ = Real.exp (-(k : ℝ) * (∑ e ∈ s, (1 - a e)) / (s.card : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      field_simp [hN.ne']
      ring

/-- Full finite sampling-without-replacement bound. -/
theorem subset_product_average_le_exp {E : Type*} (s : Finset E)
    (a : E → ℝ) (hs : 0 < s.card) (ha : ∀ e ∈ s, 0 ≤ a e)
    (k : ℕ) (hk : k ≤ s.card) :
    subsetAverage s k (fun t => ∏ e ∈ t, a e) ≤
      Real.exp (-(k : ℝ) * (∑ e ∈ s, (1 - a e)) / (s.card : ℝ)) :=
  (subset_product_average_le_mean_pow s a hs ha k hk).trans
    (mean_pow_le_exp_neg_sum_complement s a hs ha k)

/-- Any finite survival mass dominated, subset by subset, by the avoidance
product satisfies the same tail bound. The mass may already include the
indicator that a stopped epoch reaches round `k`; no conditioning on that
indicator is performed here. -/
theorem dominated_subset_average_le_exp {E : Type*} (s : Finset E)
    (a : E → ℝ) (hs : 0 < s.card) (ha : ∀ e ∈ s, 0 ≤ a e)
    (k : ℕ) (hk : k ≤ s.card) (survivalMass : Finset E → ℝ)
    (hdom : ∀ t ∈ s.powersetCard k, survivalMass t ≤ ∏ e ∈ t, a e) :
    subsetAverage s k survivalMass ≤
      Real.exp (-(k : ℝ) * (∑ e ∈ s, (1 - a e)) / (s.card : ℝ)) := by
  apply le_trans (b := subsetAverage s k (fun t => ∏ e ∈ t, a e))
  · exact div_le_div_of_nonneg_right (Finset.sum_le_sum hdom) (by positivity)
  · exact subset_product_average_le_exp s a hs ha k hk

/-- A fully finite event formulation: the inner weighted indicator is the
joint event of reaching the requested round and surviving. Any verified
product domination of that inner sum gives the without-replacement bound.
Independent levels and the actual stopped-process coupling remain inputs,
not conclusions, of this deterministic theorem. -/
theorem stopped_event_average_le_exp {E Ω : Type*} (s : Finset E)
    (a : E → ℝ) (hs : 0 < s.card) (ha : ∀ e ∈ s, 0 ≤ a e)
    (k : ℕ) (hk : k ≤ s.card) (levels : Finset Ω)
    (weight : Finset E → Ω → ℝ) (reaches survives : Finset E → Ω → Prop)
    [∀ (t : Finset E) (ω : Ω), Decidable (reaches t ω ∧ survives t ω)]
    (hdom : ∀ t ∈ s.powersetCard k,
      (∑ ω ∈ levels, if reaches t ω ∧ survives t ω then weight t ω else 0) ≤
        ∏ e ∈ t, a e) :
    subsetAverage s k
        (fun t => ∑ ω ∈ levels, if reaches t ω ∧ survives t ω then weight t ω else 0) ≤
      Real.exp (-(k : ℝ) * (∑ e ∈ s, (1 - a e)) / (s.card : ℝ)) := by
  exact dominated_subset_average_le_exp s a hs ha k hk _ hdom

end DirectedFlowCutGap.FiniteSurvival
