import OnlineReachabilityPreservers.SteinerWeightedCover

/-! Integer capacities for a weighted cut separator. -/

namespace OnlineReachabilityPreservers

open Finset

/-- The integer ceiling of the unnormalized rational capacity. -/
def roundedWeightedCapacity (cost charge : ℕ) : ℕ :=
  (weightedLoad cost charge + (cost - 1)) / cost

theorem roundedWeightedCapacity_bounds {cost : ℕ} (positive : 0 < cost) (charge : ℕ) :
    weightedCapacity cost charge ≤ (roundedWeightedCapacity cost charge : ℚ) ∧
      (roundedWeightedCapacity cost charge : ℚ) ≤ weightedCapacity cost charge + 1 := by
  let load := weightedLoad cost charge
  let cap := roundedWeightedCapacity cost charge
  have below : cap * cost ≤ load + (cost - 1) := Nat.div_mul_le_self _ _
  have above : load + (cost - 1) < cost * (cap + 1) := Nat.lt_mul_div_succ _ positive
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm cost cap] at above
  have exactLo : load ≤ cap * cost := by omega
  have exactHi : cap * cost ≤ load + cost := by omega
  have divisor : (0 : ℚ) < cost := Nat.cast_pos.mpr positive
  change (load : ℚ) / cost ≤ (cap : ℚ) ∧ (cap : ℚ) ≤ (load : ℚ) / cost + 1
  constructor
  · exact (div_le_iff₀ divisor).mpr (by exact_mod_cast exactLo)
  · calc
      (cap : ℚ) ≤ ((load : ℚ) + cost) / cost := (le_div_iff₀ divisor).mpr (by exact_mod_cast exactHi)
      _ = _ := by rw [add_div, div_self divisor.ne']

theorem roundedWeightedCapacity_mono {cost : ℕ} (positive : 0 < cost) :
    Monotone (roundedWeightedCapacity cost) := by
  intro a b h
  exact Nat.div_le_div_right (Nat.add_le_add_right (weightedLoad_mono positive h) _)

theorem weightedLoad_factors_le {cost charge scale : ℕ} (positive : 0 < cost) (scalePos : 0 < scale)
    (cap : charge ≤ (scale.log2 + 1) * cost) :
    2 ^ (charge / cost) ≤ 2 * scale ∧ cost + charge % cost ≤ 2 * cost := by
  have expo : charge / cost ≤ scale.log2 + 1 :=
    (Nat.div_le_iff_le_mul positive).mpr (by omega)
  have pow_le : 2 ^ (charge / cost) ≤ 2 * scale := by
    calc
      _ ≤ 2 ^ (scale.log2 + 1) := Nat.pow_le_pow_right (by decide) expo
      _ = 2 * 2 ^ scale.log2 := by rw [pow_succ']
      _ ≤ _ := Nat.mul_le_mul_left _ ((Nat.le_log2 scalePos.ne').mp le_rfl)
  have rem := Nat.mod_lt charge positive
  exact ⟨pow_le, by omega⟩

/-- The integer numerator used for ceiling division is polynomially
bounded in the edge weight and the fixed capacity scale. -/
theorem roundedWeightedCapacity_numerator_le {cost charge scale : ℕ} (positive : 0 < cost)
    (scalePos : 0 < scale) (cap : charge ≤ (scale.log2 + 1) * cost) :
    weightedLoad cost charge + (cost - 1) ≤ (4 * scale + 1) * cost := by
  obtain ⟨power,bump⟩ := weightedLoad_factors_le positive scalePos cap
  calc
    _ ≤ (2 * scale) * (2 * cost) + cost :=
      Nat.add_le_add (Nat.mul_le_mul power bump) (Nat.sub_le _ _)
    _ = _ := by ring

theorem roundedWeightedCapacity_le {cost charge scale : ℕ} (positive : 0 < cost) (scalePos : 0 < scale)
    (cap : charge ≤ (scale.log2 + 1) * cost) :
    roundedWeightedCapacity cost charge ≤ 4 * scale + 1 := by
  unfold roundedWeightedCapacity
  exact (Nat.div_le_div_right (roundedWeightedCapacity_numerator_le positive scalePos cap)).trans_eq
    (Nat.mul_div_cancel _ positive)

section

variable {E : Type*}

theorem weightedCutSum_le_rounded (cut : Finset E) (weight charges : E → ℕ)
    (positive : ∀ e ∈ cut, 0 < weight e) :
    weightedCutSum cut weight charges ≤
      (((∑ e ∈ cut, roundedWeightedCapacity (weight e) (charges e)) : ℕ) : ℚ) := by
  rw [Nat.cast_sum]
  exact sum_le_sum fun e he => (roundedWeightedCapacity_bounds (positive e he) _).1

theorem roundedWeightedObjective_le (edges : Finset E) (weight charges : E → ℕ)
    (positive : ∀ e ∈ edges, 0 < weight e) :
    let scale := weightedCoverScale edges weight
    (∑ e ∈ edges, (weight e : ℚ) * ((roundedWeightedCapacity (weight e) (charges e) : ℚ) / (scale : ℚ))) ≤
      (weightedObjective edges weight charges : ℚ) / (scale : ℚ) + 1 := by
  let scale := weightedCoverScale edges weight
  have scalePos : (0 : ℚ) < scale := Nat.cast_pos.mpr (zero_lt_one.trans_le (le_max_left _ _))
  have baseline : (∑ e ∈ edges, (weight e : ℚ)) / (scale : ℚ) ≤ 1 := by
    apply (div_le_iff₀ scalePos).mpr
    rw [one_mul]
    exact_mod_cast (le_max_right 1 (∑ e ∈ edges, weight e))
  change (∑ e ∈ edges, (weight e : ℚ) * ((roundedWeightedCapacity (weight e) (charges e) : ℚ) / (scale : ℚ))) ≤
    (weightedObjective edges weight charges : ℚ) / (scale : ℚ) + 1
  rw [weightedObjective_eq_capacity_sum edges weight charges positive]
  calc
    _ ≤ ∑ e ∈ edges, (weight e : ℚ) *
        ((weightedCapacity (weight e) (charges e) + 1) / (scale : ℚ)) := by
      apply sum_le_sum
      intro e he
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (roundedWeightedCapacity_bounds (positive e he) _).2 scalePos.le)
        (Nat.cast_nonneg _)
    _ = (∑ e ∈ edges, (weight e : ℚ) * (weightedCapacity (weight e) (charges e) / (scale : ℚ))) +
          (∑ e ∈ edges, (weight e : ℚ)) / (scale : ℚ) := by
      simp only [add_div, mul_add, sum_add_distrib, mul_one_div, Finset.sum_div]
    _ ≤ _ := add_le_add le_rfl baseline

end

end OnlineReachabilityPreservers
