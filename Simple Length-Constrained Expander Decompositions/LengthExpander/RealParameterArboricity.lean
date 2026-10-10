import LengthExpander.ForestPartition
import Mathlib.Algebra.Order.Floor.Semiring

/-! The source does not explicitly restrict s to integers. The exact exponent
2/s does not extend to all reals. This module states the actual all-real
consequence: round down the graph-distance threshold, or use exponent 4/s. -/
namespace LengthExpander
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure IsRealParallelGreedy (G : SimpleGraph V) (index : Sym2 V → ℕ) (s : ℝ) : Prop where
  matching : MatchingLabels G index
  earlierFar : ∀ u v, G.Adj u v → ∀ p : G.Walk u v,
    (p.length:ℝ) ≤ s → (∀ e ∈ p.edges, index e < index s(u,v)) → False

theorem real_parallelGreedy_iff_floor {index : Sym2 V → ℕ} {s : ℝ} (hs : 0 ≤ s) :
    IsRealParallelGreedy G index s ↔ IsParallelGreedy G index ⌊s⌋₊ := by
  constructor
  · intro H
    exact ⟨H.matching,fun u v huv p hp he => H.earlierFar u v huv p
      ((Nat.le_floor_iff hs).mp hp) he⟩
  · intro H
    exact ⟨H.matching,fun u v huv p hp he => H.earlierFar u v huv p
      ((Nat.le_floor_iff hs).mpr hp) he⟩

theorem floor_threshold_bounds {s : ℝ} (hs : 2 ≤ s) :
    2 ≤ ⌊s⌋₊ ∧ (⌊s⌋₊:ℝ) ≤ s ∧ s ≤ 2*(⌊s⌋₊:ℝ) := by
  have h0 : 0 ≤ s := by linarith
  have h2 : 2 ≤ ⌊s⌋₊ := Nat.le_floor (by exact_mod_cast hs)
  have h2r : (2:ℝ) ≤ ⌊s⌋₊ := by exact_mod_cast h2
  have hl := Nat.lt_floor_add_one s
  exact ⟨h2,Nat.floor_le h0,by linarith⟩

theorem rounded_density_le_smooth (n : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    8*(⌊s⌋₊:ℝ)*(n:ℝ)^(2/(⌊s⌋₊:ℝ)) ≤ 8*s*(n:ℝ)^(4/s) := by
  obtain ⟨hf,hfs,hsf⟩ := floor_threshold_bounds hs
  have hfpos : (0:ℝ) < ⌊s⌋₊ := by exact_mod_cast (show 0 < ⌊s⌋₊ by omega)
  have hspos : 0 < s := by linarith
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (by positivity : (2:ℝ)/(⌊s⌋₊:ℝ) ≠ 0),
      Real.zero_rpow (by positivity : (4:ℝ)/s ≠ 0)]
  · have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have he : (2:ℝ)/(⌊s⌋₊:ℝ) ≤ 4/s := (div_le_div_iff₀ hfpos hspos).mpr (by linarith)
    have hp := Real.rpow_le_rpow_of_exponent_le hn1 he
    have hpn := Real.rpow_nonneg (Nat.cast_nonneg n) ((4:ℝ)/s)
    nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 8*(⌊s⌋₊:ℝ))]

/-- An actual forest partition for real thresholds, with the rounded exact
integer bound and the valid smooth 4/s bound both made explicit. -/
theorem real_parallelGreedy_forest_partition {index : Sym2 V → ℕ} {s : ℝ}
    (H : IsRealParallelGreedy G index s) (hs : 2 ≤ s) :
    ∃ (K : ℕ) (P : Fin K → SimpleGraph V),
      K = densityBudget (Fintype.card V) ⌊s⌋₊ ∧
      K ≤ ⌈8*s*(Fintype.card V:ℝ)^(4/s)⌉₊ ∧
      (∀ i, (P i).IsAcyclic) ∧ (∀ i, P i ≤ G) ∧
      (∀ u v, G.Adj u v → ∃! i, (P i).Adj u v) := by
  obtain ⟨P,ha,hle,hpart⟩ := parallelGreedy_forest_partition
    ((real_parallelGreedy_iff_floor (by linarith : 0 ≤ s)).mp H)
    (floor_threshold_bounds hs).1
  refine ⟨_,P,rfl,?_,ha,hle,hpart⟩
  exact Nat.ceil_mono (rounded_density_le_smooth (Fintype.card V) hs)

end LengthExpander
