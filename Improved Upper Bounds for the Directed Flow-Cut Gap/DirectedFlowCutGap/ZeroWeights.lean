import DirectedFlowCutGap.MultiplicativeWeights

/-!
# Removing zero weights from the finite sampling reduction

An arbitrary admissibility predicate and an explicit nonnegative-cost oracle
suffice to construct the finite family.  A penalty on zero-weight items proves
that they can be avoided; avoidance is not an extra oracle assumption.

For reuse of the positive-weight recurrence, zero weights are replaced by one
and admissibility is strengthened to exclude those items.  The resulting
explicit horizon may depend on these auxiliary weights.  This file asserts
neither a graph-theoretic oracle nor a polynomial running-time bound.
-/

namespace DirectedFlowCutGap

noncomputable section

open scoped BigOperators

variable {E : Type*} [Fintype E]

/-- Positive auxiliary weights used only by the recurrence and its horizon. -/
def mwPositiveWeight (w : E → ℝ) (e : E) : ℝ :=
  if 0 < w e then w e else 1

omit [Fintype E] in
theorem mwPositiveWeight_pos (w : E → ℝ) (e : E) :
    0 < mwPositiveWeight w e := by
  unfold mwPositiveWeight
  split_ifs with h
  · exact h
  · norm_num

omit [Fintype E] in
theorem le_mwPositiveWeight (w : E → ℝ) (e : E) :
    w e ≤ mwPositiveWeight w e := by
  unfold mwPositiveWeight
  split_ifs with h
  · exact le_rfl
  · linarith

/-- Including `1` makes the minimum well-defined even for an empty item type. -/
def mwPositiveMinimum (w : E → ℝ) : ℝ :=
  (insert 1 (Finset.univ.image (mwPositiveWeight w))).min'
    (Finset.insert_nonempty _ _)

theorem mwPositiveMinimum_pos (w : E → ℝ) :
    0 < mwPositiveMinimum w := by
  unfold mwPositiveMinimum
  have hm := Finset.min'_mem (insert 1 (Finset.univ.image (mwPositiveWeight w)))
    (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp hm with hm | hm
  · simpa only [hm] using (show (0 : ℝ) < 1 by norm_num)
  · obtain ⟨e, _, he⟩ := Finset.mem_image.mp hm
    rw [← he]
    exact mwPositiveWeight_pos w e

theorem mwPositiveMinimum_le (w : E → ℝ) (e : E) :
    mwPositiveMinimum w ≤ mwPositiveWeight w e := by
  exact Finset.min'_le _ _
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩))

/-- A zero approximation factor forces the empty set to be admissible. -/
theorem mw_empty_admissible_of_zero
    (w : E → ℝ) (P : Finset E → Prop)
    (horacle : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, c e) ≤ 0 * mwPotential w c) :
    P ∅ := by
  obtain ⟨X, hP, hX⟩ := horacle (fun _ => 1) (fun _ => by norm_num)
  have hcard : (X.card : ℝ) ≤ 0 := by simpa using hX
  have hempty : X = ∅ := Finset.card_eq_zero.mp
    (Nat.le_zero.mp (by exact_mod_cast hcard))
  simpa [hempty] using hP

/--
Penalizing every zero-weight item above the entire oracle budget proves that
the original oracle supplies an admissible set avoiding all such items.
-/
theorem mw_oracle_avoids_zero
    (w : E → ℝ) (α : ℝ) (P : Finset E → Prop)
    (hw : ∀ e, 0 ≤ w e) (hα : 0 ≤ α)
    (horacle : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, c e) ≤ α * mwPotential w c)
    (c : E → ℝ) (hc : ∀ e, 0 ≤ c e) :
    ∃ X : Finset E, P X ∧ (∀ e ∈ X, 0 < w e) ∧
      (∑ e ∈ X, c e) ≤ α * mwPotential w c := by
  let B : ℝ := α * mwPotential w c + 1
  let d : E → ℝ := fun e => if 0 < w e then c e else B
  have hpotential : 0 ≤ mwPotential w c :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (hc e) (hw e))
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hd (e : E) : 0 ≤ d e := by
    dsimp [d]
    split_ifs
    · exact hc e
    · exact hB
  have hsame : mwPotential w d = mwPotential w c := by
    unfold mwPotential
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : 0 < w e
    · simp [d, he]
    · have hz : w e = 0 := le_antisymm (le_of_not_gt he) (hw e)
      simp [hz]
  obtain ⟨X, hP, hX⟩ := horacle d hd
  rw [hsame] at hX
  have havoid (e : E) (he : e ∈ X) : 0 < w e := by
    by_contra hn
    have hsingle : d e ≤ ∑ a ∈ X, d a :=
      Finset.single_le_sum (fun a _ => hd a) he
    have hde : d e = B := by simp [d, hn]
    rw [hde] at hsingle
    dsimp [B] at hsingle
    linarith
  refine ⟨X, hP, havoid, ?_⟩
  have hcost : (∑ e ∈ X, d e) = ∑ e ∈ X, c e := by
    apply Finset.sum_congr rfl
    intro e he
    simp [d, havoid e he]
  rwa [hcost] at hX

/-- The explicit horizon for nonnegative weights, with one round when `α = 0`. -/
def mwNonnegativeHorizon (w : E → ℝ) (α : ℝ) : ℕ :=
  if α = 0 then 1 else mwHorizon (mwPositiveWeight w) α (mwPositiveMinimum w)

theorem mwNonnegativeHorizon_pos (w : E → ℝ) (α : ℝ) :
    0 < mwNonnegativeHorizon w α := by
  unfold mwNonnegativeHorizon
  split_ifs
  · norm_num
  · exact Nat.zero_lt_succ _

variable [DecidableEq E]

/--
The finite oracle-to-family reduction for every nonnegative weight vector and
nonnegative approximation factor, including both degenerate cases.  Every
member is admissible, every zero-weight item is absent, and all inclusion
fractions are at most `4 * α * w e`.
-/
theorem exists_nonnegative_mw_family
    (w : E → ℝ) (α : ℝ) (P : Finset E → Prop)
    (hw : ∀ e, 0 ≤ w e) (hα : 0 ≤ α)
    (horacle : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, c e) ≤ α * mwPotential w c) :
    ∃ X : Fin (mwNonnegativeHorizon w α) → Finset E,
      (∀ i, P (X i)) ∧ (∀ i e, e ∈ X i → 0 < w e) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) /
        (mwNonnegativeHorizon w α : ℝ) ≤ 4 * α * w e := by
  by_cases hzero : α = 0
  · subst α
    have hP := mw_empty_admissible_of_zero w P horacle
    refine ⟨fun _ => ∅, fun _ => hP, ?_, ?_⟩
    · simp
    · simp
  · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hzero)
    let Q : Finset E → Prop := fun X => P X ∧ ∀ e ∈ X, 0 < w e
    have haux : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
        ∃ X : Finset E, Q X ∧
          (∑ e ∈ X, c e) ≤ α * mwPotential (mwPositiveWeight w) c := by
      intro c hc
      obtain ⟨X, hP, havoid, hcost⟩ :=
        mw_oracle_avoids_zero w α P hw hα horacle c hc
      refine ⟨X, ⟨hP, havoid⟩, hcost.trans ?_⟩
      apply mul_le_mul_of_nonneg_left _ hα
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left (le_mwPositiveWeight w e) (hc e)
    obtain ⟨X, hQ, hX⟩ := exists_finite_mw_family
      (mwPositiveWeight w) α (mwPositiveMinimum w) Q
      (mwPositiveMinimum_pos w) (mwPositiveMinimum_le w) hαpos haux
    rw [show mwNonnegativeHorizon w α =
      mwHorizon (mwPositiveWeight w) α (mwPositiveMinimum w) by
        simp [mwNonnegativeHorizon, hzero]]
    refine ⟨X, fun i => (hQ i).1, fun i e he => (hQ i).2 e he, ?_⟩
    intro e
    by_cases he : 0 < w e
    · simpa [mwPositiveWeight, he, mul_comm, mul_left_comm] using hX e
    · have habsent : ∀ i, e ∉ X i := fun i hi => he ((hQ i).2 e hi)
      have hz : w e = 0 := le_antisymm (le_of_not_gt he) (hw e)
      simp [habsent, hz]

/-- An existential form with a strictly positive finite number of rounds. -/
theorem exists_finite_nonnegative_mw_family
    (w : E → ℝ) (α : ℝ) (P : Finset E → Prop)
    (hw : ∀ e, 0 ≤ w e) (hα : 0 ≤ α)
    (horacle : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, c e) ≤ α * mwPotential w c) :
    ∃ T : ℕ, 0 < T ∧ ∃ X : Fin T → Finset E,
      (∀ i, P (X i)) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) / (T : ℝ) ≤
        4 * α * w e := by
  obtain ⟨X, hP, _, hX⟩ := exists_nonnegative_mw_family w α P hw hα horacle
  exact ⟨mwNonnegativeHorizon w α, mwNonnegativeHorizon_pos w α, X, hP, hX⟩

end

end DirectedFlowCutGap
