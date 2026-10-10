import DirectedFlowCutGap.RawNonnegativeRational

/-!
# Failure tolerance at the unchanged original weights

On the branch where no empty valid cut exists, the unit-cost instance of the
all-cost guarantee forces `1 ≤ α * W`. This module derives a dyadic tolerance
from the actual encoded input width and resource count, even when `α < 1`.
It neither implements the empty-cut decision nor assumes that a failed random
query can certify it. The adaptive probability and binary sampler joins remain
separate. In an edge application, the resource family must consist of actual
original edges; nonedge fillers must not be included in `W`.
-/
namespace DirectedFlowCutGap.WeightedFailureBudget
open scoped BigOperators NNRat NNReal
open RawNonnegativeRational

noncomputable def weight (q : Code) : ℝ := q.num / (q.den : ℝ)

theorem weight_eq_value (q : Code) : weight q = (q.value : ℝ) := by
  simp [weight,Code.value]

theorem weight_nonneg (q : Code) : 0 ≤ weight q := by
  unfold weight
  positivity

theorem weight_upper (q : Code) (B : ℕ) (h : q.Bounded B) :
    weight q ≤ (2 : ℝ)^B := by
  have hd : (1 : ℝ) ≤ q.den := by exact_mod_cast q.positive_den
  have hn : (q.num : ℝ) ≤ (2 : ℝ)^B := by exact_mod_cast h.1
  have hp : 0 < (q.den : ℝ) := by exact_mod_cast q.positive_den
  apply (div_le_iff₀ hp).2
  exact hn.trans (le_mul_of_one_le_right (by positivity) hd)

theorem positive_weight_lower (q : Code) (B : ℕ) (h : q.Bounded B)
    (hq : 0 < weight q) : 1 / (2 : ℝ)^B ≤ weight q := by
  have hd : 0 < (q.den : ℝ) := by exact_mod_cast q.positive_den
  have hn : 0 < (q.num : ℝ) := (div_pos_iff_of_pos_right hd).mp hq
  have hnN : 0 < q.num := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ q.num := by exact_mod_cast hnN
  have hdB : (q.den : ℝ) ≤ (2 : ℝ)^B := by exact_mod_cast h.2
  unfold weight
  apply (div_le_div_iff₀ (by positivity : 0 < (2 : ℝ)^B) hd).2
  calc
    1 * (q.den : ℝ) ≤ (2 : ℝ)^B := by simpa using hdB
    _ ≤ (q.num : ℝ) * (2 : ℝ)^B := le_mul_of_one_le_left (by positivity) hn1

variable {A : Type*} [Fintype A]

noncomputable def totalWeight (c : A → Code) : ℝ := ∑ i, weight (c i)

theorem totalWeight_nonneg (c : A → Code) : 0 ≤ totalWeight c :=
  Finset.sum_nonneg fun i _ => weight_nonneg (c i)

theorem totalWeight_upper (c : A → Code) (B : ℕ) (h : ∀ i, (c i).Bounded B) :
    totalWeight c ≤ Fintype.card A * (2 : ℝ)^B := by
  calc
    totalWeight c ≤ ∑ _i : A, (2 : ℝ)^B :=
      Finset.sum_le_sum fun i _ => weight_upper (c i) B (h i)
    _ = _ := by simp

omit [Fintype A] in
/-- This is the precise unit-cost consequence used after an independently
certified nonempty-cut branch. It does not identify an ideal choice with code. -/
theorem nonempty_unit_cost {family : Set (Finset A)} {α W : ℝ}
    (hempty : (∅ : Finset A) ∉ family)
    (hunit : ∃ cut ∈ family, (cut.card : ℝ) ≤ α * W) : 1 ≤ α * W := by
  obtain ⟨cut,hcut,hbound⟩ := hunit
  have hn : cut.Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun he => hempty (he ▸ hcut))
  have hc : (1 : ℝ) ≤ cut.card := by exact_mod_cast Finset.card_pos.mpr hn
  exact hc.trans hbound

def exponent (m B : ℕ) : ℕ := 2*B + Nat.size m

noncomputable def tolerance (m B : ℕ) : ℝ := 1 / (2 : ℝ)^(exponent m B)

theorem tolerance_pos (m B : ℕ) : 0 < tolerance m B := by
  unfold tolerance
  positivity

/-- A polynomial-size trial exponent suffices without normalizing the input
weights or requiring the approximation factor to be at least one. -/
theorem tolerance_le_scaled_weight (c : A → Code) (B : ℕ)
    (h : ∀ i, (c i).Bounded B) {α : ℝ} (hα : 0 ≤ α)
    (hunit : 1 ≤ α * totalWeight c) (i : A) (hi : 0 < weight (c i)) :
    tolerance (Fintype.card A) B ≤ α * weight (c i) := by
  let P : ℝ := (2 : ℝ)^B
  let m : ℕ := Fintype.card A
  have hP : 0 < P := by dsimp [P]; positivity
  have hw : 1 ≤ P * weight (c i) := by
    have hh := positive_weight_lower (c i) B (h i) hi
    have hh' := (div_le_iff₀ hP).mp hh
    simpa only [mul_comm] using hh'
  have hfirst : 1 ≤ α * ((m : ℝ)*P) :=
    hunit.trans (mul_le_mul_of_nonneg_left (totalWeight_upper c B h) hα)
  have hproduct : 1 ≤ (α*((m : ℝ)*P))*(P*weight (c i)) := by
    have hh := mul_le_mul hfirst hw (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
    simpa using hh
  have hm : (m : ℝ) ≤ (2 : ℝ)^(Nat.size m) := by
    exact_mod_cast (Nat.lt_size_self m).le
  have hαw : 0 ≤ α * weight (c i) := mul_nonneg hα hi.le
  have hscale : (m : ℝ) * P^2 * (α*weight (c i)) ≤
      (2 : ℝ)^(Nat.size m) * P^2 * (α*weight (c i)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (sq_nonneg P)) hαw
  have heq : (2 : ℝ)^(Nat.size m) * P^2 = (2 : ℝ)^(exponent m B) := by
    dsimp [P,exponent]
    rw [pow_add,Nat.mul_comm 2 B,pow_mul]
    ring
  have hlower : 1 ≤ (2 : ℝ)^(exponent m B) * (α*weight (c i)) := by
    rw [← heq]
    apply le_trans ?_ hscale
    nlinarith [hproduct]
  exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ)^(exponent m B))).2
    (by simpa only [mul_comm] using hlower)

theorem exponent_bound (m B : ℕ) : exponent m B ≤ 2*B+m := by
  exact Nat.add_le_add_left (Nat.size_le.mpr Nat.lt_two_pow_self) _

end DirectedFlowCutGap.WeightedFailureBudget
