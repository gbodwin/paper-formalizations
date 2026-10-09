import Mathlib

/-!
# A scaled finite multiplicative-weights reduction

This file formalizes an auxiliary repair to the sampling argument on printed
pages 31–32 of Bodwin–Samborska, arXiv:2604.03412v3.  It does not assert the
main flow-cut theorem.  In particular, the update below has a common scale
`η`; the unscaled update in the printed proof does not justify its logarithm
estimate when the product of the weight and the approximation factor is small.

All items in this file have strictly positive weights.  Removing zero-weight
items and supplying the graph-theoretic cut oracle are separate obligations.
-/

namespace DirectedFlowCutGap

noncomputable section

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The weighted cost potential. -/
def mwPotential (w c : E → ℝ) : ℝ := ∑ e, c e * w e

/-- The cost associated with a vector of selection counts. -/
def mwCost (w : E → ℝ) (α η : ℝ) (k : E → ℕ) (e : E) : ℝ :=
  (1 + η / (w e * α)) ^ k e

/-- Counts generated internally by repeatedly querying a cost oracle. -/
def mwCount (w : E → ℝ) (α η : ℝ)
    (choose : (E → ℝ) → Finset E) : ℕ → E → ℕ
  | 0 => fun _ => 0
  | t + 1 => fun e => mwCount w α η choose t e +
      if e ∈ choose (mwCost w α η (mwCount w α η choose t)) then 1 else 0

/-- The cut selected at round `t`. -/
def mwCut (w : E → ℝ) (α η : ℝ)
    (choose : (E → ℝ) → Finset E) (t : ℕ) : Finset E :=
  choose (mwCost w α η (mwCount w α η choose t))

omit [Fintype E] in
@[simp] theorem mwCount_zero (w : E → ℝ) (α η : ℝ)
    (choose : (E → ℝ) → Finset E) (e : E) :
    mwCount w α η choose 0 e = 0 := rfl

omit [Fintype E] in
theorem mwCount_succ (w : E → ℝ) (α η : ℝ)
    (choose : (E → ℝ) → Finset E) (t : ℕ) (e : E) :
    mwCount w α η choose (t + 1) e =
      mwCount w α η choose t e + if e ∈ mwCut w α η choose t then 1 else 0 := rfl

omit [Fintype E] [DecidableEq E] in
theorem mwCost_pos (w : E → ℝ) (α η : ℝ)
    (hw : ∀ e, 0 < w e) (hα : 0 < α) (hη : 0 ≤ η)
    (k : E → ℕ) (e : E) : 0 < mwCost w α η k e := by
  unfold mwCost
  apply pow_pos
  have := div_nonneg hη (mul_pos (hw e) hα).le
  linarith

omit [Fintype E] in
theorem mwCost_succ (w : E → ℝ) (α η : ℝ)
    (choose : (E → ℝ) → Finset E) (t : ℕ) (e : E) :
    mwCost w α η (mwCount w α η choose (t + 1)) e =
      mwCost w α η (mwCount w α η choose t) e *
        if e ∈ mwCut w α η choose t then 1 + η / (w e * α) else 1 := by
  simp only [mwCost, mwCount_succ, pow_add]
  split_ifs <;> simp

/-- The potential increment is exactly the scaled cost of the chosen cut. -/
theorem mwPotential_succ (w : E → ℝ) (α η : ℝ)
    (hw : ∀ e, 0 < w e) (hα : 0 < α)
    (choose : (E → ℝ) → Finset E) (t : ℕ) :
    mwPotential w (mwCost w α η (mwCount w α η choose (t + 1))) =
      mwPotential w (mwCost w α η (mwCount w α η choose t)) +
        η / α * ∑ e ∈ mwCut w α η choose t,
          mwCost w α η (mwCount w α η choose t) e := by
  have pointwise (e : E) :
      mwCost w α η (mwCount w α η choose (t + 1)) e * w e =
        mwCost w α η (mwCount w α η choose t) e * w e +
          if e ∈ mwCut w α η choose t then
            η / α * mwCost w α η (mwCount w α η choose t) e else 0 := by
    rw [mwCost_succ]
    split_ifs
    · field_simp [ne_of_gt (hw e), ne_of_gt hα]
    · ring
  unfold mwPotential
  simp_rw [pointwise, Finset.sum_add_distrib]
  simp [Finset.mul_sum]

/-- A valid cost oracle increases the weighted potential by at most `1 + η` per round. -/
theorem mwPotential_le (w : E → ℝ) (α η : ℝ)
    (hw : ∀ e, 0 < w e) (hα : 0 < α) (hη : 0 ≤ η)
    (choose : (E → ℝ) → Finset E)
    (hchoose : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      (∑ e ∈ choose c, c e) ≤ α * mwPotential w c) (t : ℕ) :
    mwPotential w (mwCost w α η (mwCount w α η choose t)) ≤
      (∑ e, w e) * (1 + η) ^ t := by
  induction t with
  | zero => simp [mwPotential, mwCost, mwCount]
  | succ t ih =>
    rw [mwPotential_succ w α η hw hα]
    have hc := hchoose (mwCost w α η (mwCount w α η choose t))
      (fun e => (mwCost_pos w α η hw hα hη _ e).le)
    change (∑ e ∈ mwCut w α η choose t,
      mwCost w α η (mwCount w α η choose t) e) ≤ _ at hc
    have hs := mul_le_mul_of_nonneg_left hc (div_nonneg hη hα.le)
    have hcancel : η / α * (α * mwPotential w
        (mwCost w α η (mwCount w α η choose t))) =
        η * mwPotential w (mwCost w α η (mwCount w α η choose t)) := by
      field_simp
    rw [hcancel] at hs
    have hi := mul_le_mul_of_nonneg_right ih (show 0 ≤ 1 + η by linarith)
    rw [pow_succ]
    nlinarith

omit [DecidableEq E] in
/-- Each single item's weighted cost is bounded by the whole potential. -/
theorem mwCost_mul_weight_le (w : E → ℝ) (α η : ℝ)
    (hw : ∀ e, 0 < w e) (hα : 0 < α) (hη : 0 ≤ η)
    (k : E → ℕ) (e : E) :
    mwCost w α η k e * w e ≤ mwPotential w (mwCost w α η k) := by
  unfold mwPotential
  exact Finset.single_le_sum (f := fun a => mwCost w α η k a * w a)
    (fun a _ => mul_nonneg (mwCost_pos w α η hw hα hη k a).le (hw a).le)
    (Finset.mem_univ e)

/-- The logarithmic estimate before imposing a bound on the scaled update. -/
theorem mwCount_log_bound (w : E → ℝ) (α η : ℝ)
    (hw : ∀ e, 0 < w e) (hα : 0 < α) (hη : 0 ≤ η)
    (choose : (E → ℝ) → Finset E)
    (hchoose : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      (∑ e ∈ choose c, c e) ≤ α * mwPotential w c)
    (t : ℕ) (e : E) :
    (mwCount w α η choose t e : ℝ) * Real.log (1 + η / (w e * α)) ≤
      (t : ℝ) * η + Real.log ((∑ a, w a) / w e) := by
  have hW : 0 < ∑ a, w a := lt_of_lt_of_le (hw e)
    (Finset.single_le_sum (fun a _ => (hw a).le) (Finset.mem_univ e))
  have hbase : 0 < 1 + η / (w e * α) := by
    have := div_nonneg hη (mul_pos (hw e) hα).le
    linarith
  have hbase' : 0 < 1 + η := by linarith
  have hpow := (mwCost_mul_weight_le w α η hw hα hη
    (mwCount w α η choose t) e).trans
    (mwPotential_le w α η hw hα hη choose hchoose t)
  have hlog := Real.log_le_log
    (mul_pos (mwCost_pos w α η hw hα hη _ e) (hw e)) hpow
  rw [Real.log_mul (ne_of_gt (mwCost_pos w α η hw hα hη _ e)) (hw e).ne',
    Real.log_mul hW.ne' (pow_ne_zero t hbase'.ne')] at hlog
  simp only [mwCost, Real.log_pow] at hlog
  have heta := Real.log_le_sub_one_of_pos hbase'
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hmul := mul_le_mul_of_nonneg_left heta ht
  rw [Real.log_div hW.ne' (hw e).ne']
  nlinarith

/-- The elementary logarithm estimate used only in its valid range. -/
theorem mw_half_le_log_one_add {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ Real.log (1 + x) := by
  have hlog := Real.le_log_one_add_of_nonneg hx
  have hden : 0 < x + 2 := by linarith
  have hfrac : x / 2 ≤ 2 * x / (x + 2) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  exact hfrac.trans hlog

/-- The scaled recurrence yields the desired weight-proportional count bound. -/
theorem mwCount_le (w : E → ℝ) (α η : ℝ)
    (hw : ∀ e, 0 < w e) (hα : 0 < α) (hη : 0 < η)
    (hscale : ∀ e, η ≤ w e * α)
    (choose : (E → ℝ) → Finset E)
    (hchoose : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      (∑ e ∈ choose c, c e) ≤ α * mwPotential w c)
    (t : ℕ) (e : E) :
    (mwCount w α η choose t e : ℝ) ≤
      2 * (w e * α) * ((t : ℝ) + Real.log ((∑ a, w a) / w e) / η) := by
  have hx : 0 < w e * α := mul_pos (hw e) hα
  have hz : 0 ≤ η / (w e * α) := (div_pos hη hx).le
  have hz1 : η / (w e * α) ≤ 1 := (div_le_one hx).2 (hscale e)
  have hlower := mul_le_mul_of_nonneg_left (mw_half_le_log_one_add hz hz1)
    (Nat.cast_nonneg (mwCount w α η choose t e))
  have hbound := hlower.trans (mwCount_log_bound w α η hw hα hη.le choose hchoose t e)
  apply (mul_le_mul_iff_left₀ hη).mp
  calc
    (mwCount w α η choose t e : ℝ) * η =
        ((mwCount w α η choose t e : ℝ) * (η / (w e * α) / 2)) *
          (2 * (w e * α)) := by field_simp [(hw e).ne', hα.ne']
    _ ≤ ((t : ℝ) * η + Real.log ((∑ a, w a) / w e)) * (2 * (w e * α)) :=
      mul_le_mul_of_nonneg_right hbound (mul_nonneg (by norm_num) hx.le)
    _ = (2 * (w e * α) *
        ((t : ℝ) + Real.log ((∑ a, w a) / w e) / η)) * η := by
      field_simp [hη.ne']

/-- At a sufficient horizon, each item occurs in at most `4 * w e * α * t` rounds. -/
theorem mwCount_le_four (w : E → ℝ) (α η : ℝ)
    (hw : ∀ e, 0 < w e) (hα : 0 < α) (hη : 0 < η)
    (hscale : ∀ e, η ≤ w e * α)
    (choose : (E → ℝ) → Finset E)
    (hchoose : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      (∑ e ∈ choose c, c e) ≤ α * mwPotential w c)
    (t : ℕ) (e : E)
    (ht : Real.log ((∑ a, w a) / w e) ≤ η * (t : ℝ)) :
    (mwCount w α η choose t e : ℝ) ≤ 4 * w e * α * (t : ℝ) := by
  have hdiv : Real.log ((∑ a, w a) / w e) / η ≤ (t : ℝ) := by
    apply (div_le_iff₀ hη).2
    simpa [mul_comm] using ht
  have hbound := mwCount_le w α η hw hα hη hscale choose hchoose t e
  have hmul := mul_le_mul_of_nonneg_left hdiv
    (show 0 ≤ 2 * (w e * α) from mul_nonneg (by norm_num) (mul_pos (hw e) hα).le)
  nlinarith

omit [Fintype E] in
/-- The recurrence counts actual membership among the first `t` oracle outputs. -/
theorem mwCount_eq_card (w : E → ℝ) (α η : ℝ)
    (choose : (E → ℝ) → Finset E) (t : ℕ) (e : E) :
    mwCount w α η choose t e =
      ((Finset.range t).filter fun i => e ∈ mwCut w α η choose i).card := by
  induction t with
  | zero => simp
  | succ t ih =>
    by_cases he : e ∈ mwCut w α η choose t
    · simp [mwCount_succ, Finset.range_add_one, Finset.filter_insert, he, ih]
    · simp [mwCount_succ, Finset.range_add_one, Finset.filter_insert, he, ih]

omit [Fintype E] in
/-- Equivalently, the counts are the cardinalities of fibers of a finite family. -/
theorem mwCount_eq_fin_card (w : E → ℝ) (α η : ℝ)
    (choose : (E → ℝ) → Finset E) (t : ℕ) (e : E) :
    mwCount w α η choose t e =
      (Finset.univ.filter fun i : Fin t => e ∈ mwCut w α η choose i.val).card := by
  rw [mwCount_eq_card, Finset.card_filter, Finset.card_filter]
  exact (Fin.sum_univ_eq_sum_range
    (fun i => if e ∈ mwCut w α η choose i then (1 : ℕ) else 0) t).symm

/-- Make a selector from the explicit existential cost-oracle hypothesis. -/
def mwOracleChoice (w : E → ℝ) (α : ℝ) (P : Finset E → Prop)
    (horacle : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, c e) ≤ α * mwPotential w c)
    (c : E → ℝ) : Finset E := by
  classical
  exact if hc : ∀ e, 0 ≤ c e then (horacle c hc).choose else ∅

omit [DecidableEq E] in
theorem mwOracleChoice_spec (w : E → ℝ) (α : ℝ) (P : Finset E → Prop)
    (horacle : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, c e) ≤ α * mwPotential w c)
    (c : E → ℝ) (hc : ∀ e, 0 ≤ c e) :
    P (mwOracleChoice w α P horacle c) ∧
      (∑ e ∈ mwOracleChoice w α P horacle c, c e) ≤ α * mwPotential w c := by
  classical
  simp only [mwOracleChoice, dite_eq_left hc]
  exact (horacle c hc).choose_spec

/--
A genuine finite oracle-to-family reduction for positive weights.  The family
is constructed by the recurrence above from the existential cost oracle;
neither its members nor their marginal bounds are supplied as assumptions.
-/
theorem exists_mw_family (w : E → ℝ) (α η : ℝ) (P : Finset E → Prop)
    (hw : ∀ e, 0 < w e) (hα : 0 < α) (hη : 0 < η)
    (hscale : ∀ e, η ≤ w e * α)
    (horacle : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, c e) ≤ α * mwPotential w c)
    (t : ℕ)
    (ht : ∀ e, Real.log ((∑ a, w a) / w e) ≤ η * (t : ℝ)) :
    ∃ X : Fin t → Finset E, (∀ i, P (X i)) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) ≤
        4 * w e * α * (t : ℝ) := by
  let choose := mwOracleChoice w α P horacle
  have hchoose (c : E → ℝ) (hc : ∀ e, 0 ≤ c e) :
      (∑ e ∈ choose c, c e) ≤ α * mwPotential w c :=
    (mwOracleChoice_spec w α P horacle c hc).2
  refine ⟨fun i => mwCut w α η choose i.val, ?_, ?_⟩
  · intro i
    exact (mwOracleChoice_spec w α P horacle _
      (fun e => (mwCost_pos w α η hw hα hη.le _ e).le)).1
  · intro e
    rw [← mwCount_eq_fin_card]
    exact mwCount_le_four w α η hw hα hη hscale choose hchoose t e (ht e)

/-- Uniformly sampling the constructed finite family has the claimed marginals. -/
theorem exists_mw_family_marginals (w : E → ℝ) (α η : ℝ) (P : Finset E → Prop)
    (hw : ∀ e, 0 < w e) (hα : 0 < α) (hη : 0 < η)
    (hscale : ∀ e, η ≤ w e * α)
    (horacle : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, c e) ≤ α * mwPotential w c)
    (t : ℕ) (htpos : 0 < t)
    (ht : ∀ e, Real.log ((∑ a, w a) / w e) ≤ η * (t : ℝ)) :
    ∃ X : Fin t → Finset E, (∀ i, P (X i)) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) / (t : ℝ) ≤
        4 * w e * α := by
  obtain ⟨X, hP, hX⟩ := exists_mw_family w α η P hw hα hη hscale horacle t ht
  refine ⟨X, hP, fun e => ?_⟩
  exact (div_le_iff₀ (Nat.cast_pos.mpr htpos)).2 (hX e)

/-- A single minimum-weight horizon suffices for all items. -/
theorem exists_mw_family_of_min_weight
    (w : E → ℝ) (α η wmin : ℝ) (P : Finset E → Prop)
    (hwmin : 0 < wmin) (hw : ∀ e, wmin ≤ w e)
    (hα : 0 < α) (hη : 0 < η) (hscale : η ≤ wmin * α)
    (horacle : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, c e) ≤ α * mwPotential w c)
    (t : ℕ) (htpos : 0 < t)
    (ht : Real.log ((∑ a, w a) / wmin) ≤ η * (t : ℝ)) :
    ∃ X : Fin t → Finset E, (∀ i, P (X i)) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) / (t : ℝ) ≤
        4 * w e * α := by
  have hwpos (e : E) : 0 < w e := hwmin.trans_le (hw e)
  refine exists_mw_family_marginals w α η P hwpos hα hη
    (fun e => hscale.trans (mul_le_mul_of_nonneg_right (hw e) hα.le))
    horacle t htpos ?_
  intro e
  have hW : 0 < ∑ a, w a := lt_of_lt_of_le (hwpos e)
    (Finset.single_le_sum (fun a _ => (hwpos a).le) (Finset.mem_univ e))
  have hratio : (∑ a, w a) / w e ≤ (∑ a, w a) / wmin := by
    apply (div_le_div_iff₀ (hwpos e) hwmin).2
    exact mul_le_mul_of_nonneg_left (hw e) hW.le
  exact (Real.log_le_log (div_pos hW (hwpos e)) hratio).trans ht

/-- A common scale that always satisfies the small-update condition. -/
def mwScale (α wmin : ℝ) : ℝ := min 1 (wmin * α)

/-- An explicit positive finite horizon for the common scale. -/
def mwHorizon (w : E → ℝ) (α wmin : ℝ) : ℕ :=
  ⌈Real.log ((∑ a, w a) / wmin) / mwScale α wmin⌉₊ + 1

/--
The finite positive-weight oracle reduction with an explicit choice of scale
and number of rounds.  The cardinality of the family is exactly `mwHorizon`.
This is an existence statement; computational implementation of the oracle
and its bit complexity are not asserted here.
-/
theorem exists_finite_mw_family
    (w : E → ℝ) (α wmin : ℝ) (P : Finset E → Prop)
    (hwmin : 0 < wmin) (hw : ∀ e, wmin ≤ w e) (hα : 0 < α)
    (horacle : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, c e) ≤ α * mwPotential w c) :
    ∃ X : Fin (mwHorizon w α wmin) → Finset E, (∀ i, P (X i)) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) /
        (mwHorizon w α wmin : ℝ) ≤ 4 * w e * α := by
  have hscale : 0 < mwScale α wmin := lt_min (by norm_num) (mul_pos hwmin hα)
  apply exists_mw_family_of_min_weight w α (mwScale α wmin) wmin P
    hwmin hw hα hscale (min_le_right _ _) horacle
    (mwHorizon w α wmin) (Nat.zero_lt_succ _)
  have hceil := Nat.le_ceil (Real.log ((∑ a, w a) / wmin) / mwScale α wmin)
  have ht : Real.log ((∑ a, w a) / wmin) / mwScale α wmin ≤
      (mwHorizon w α wmin : ℝ) := by
    unfold mwHorizon
    push_cast
    linarith
  have := (div_le_iff₀ hscale).1 ht
  simpa [mul_comm] using this

end

end DirectedFlowCutGap
