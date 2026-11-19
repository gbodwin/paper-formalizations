import OnlineReachabilityPreservers.Basic

/-! Counting crossings in the consecutive blocks of a rooted height reduction. -/

namespace OnlineReachabilityPreservers

open Finset

/-- Child blocks with a terminal in the interval and a terminal outside it
in the same parent block. Terminals are numbered in traversal order. -/
def terminalIntervalCrossings (terminals width branch first past : ℕ) : Finset ℕ :=
  (range terminals).filter fun child =>
    ∃ inside ∈ range terminals, inside / width = child ∧ first ≤ inside ∧ inside < past ∧
      ∃ outside ∈ range terminals, outside / (width * branch) = child / branch ∧
        ¬ (first ≤ outside ∧ outside < past)

private theorem childBlock_mem {child parent branch : ℕ} (positive : 0 < branch)
    (eq : child / branch = parent) :
    child ∈ Ico (parent * branch) ((parent + 1) * branch) := by
  refine mem_Ico.mpr ⟨(Nat.le_div_iff_mul_le positive).mp eq.ge, ?_⟩
  exact (Nat.div_lt_iff_lt_mul positive).mp (eq ▸ Nat.lt_succ_self (child / branch))

private theorem childBlock_card (parent branch : ℕ) :
    (Ico (parent * branch) ((parent + 1) * branch)).card = branch := by
  rw [Nat.card_Ico, Nat.add_mul, Nat.one_mul]
  omega

/-- At one level, only the parent blocks at the two interval boundaries can
contribute a crossing. Each has at most `branch` children. -/
theorem terminalIntervalCrossings_card (terminals width branch first past : ℕ)
    (positive : 0 < branch) :
    (terminalIntervalCrossings terminals width branch first past).card ≤ 2 * branch := by
  let firstBlock := first / (width * branch)
  let pastBlock := past / (width * branch)
  let children (parent : ℕ) := Ico (parent * branch) ((parent + 1) * branch)
  have cover : terminalIntervalCrossings terminals width branch first past ⊆
      children firstBlock ∪ children pastBlock := by
    intro child mem
    obtain ⟨inside, _, hin, left, right, outside, _, elem, apart⟩ := (mem_filter.mp mem).2
    have inner : inside / (width * branch) = child / branch := by
      rw [← Nat.div_div_eq_div_mul, hin]
    by_cases below : outside < first
    · have parent : child / branch = firstBlock := by
        apply le_antisymm
        · rw [← elem]
          exact Nat.div_le_div_right below.le
        · rw [← inner]
          exact Nat.div_le_div_right left
      exact mem_union_left _ (childBlock_mem positive parent)
    · have above : past ≤ outside := by omega
      have parent : child / branch = pastBlock := by
        apply le_antisymm
        · rw [← inner]
          exact Nat.div_le_div_right right.le
        · rw [← elem]
          exact Nat.div_le_div_right above
      exact mem_union_right _ (childBlock_mem positive parent)
  calc
    _ ≤ (children firstBlock ∪ children pastBlock).card := card_le_card cover
    _ ≤ (children firstBlock).card + (children pastBlock).card := card_union_le _ _
    _ = _ := by
      unfold children
      rw [childBlock_card, childBlock_card, two_mul]

/-- Across the given number of consecutive-block levels, a fixed terminal
interval is crossed at most twice the branch count per level. -/
theorem terminalIntervalCrossings_total (terminals branch levels first past : ℕ)
    (positive : 0 < branch) :
    (∑ level ∈ range levels,
       (terminalIntervalCrossings terminals (branch ^ level) branch first past).card) ≤
       2 * branch * levels := by
  calc
    _ ≤ ∑ _level ∈ range levels, (2 * branch) :=
      sum_le_sum fun level _ => terminalIntervalCrossings_card terminals _ branch first past positive
    _ = _ := by simp [Nat.mul_comm]

end OnlineReachabilityPreservers
