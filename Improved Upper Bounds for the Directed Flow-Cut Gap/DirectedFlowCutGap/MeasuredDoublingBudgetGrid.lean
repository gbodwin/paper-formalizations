import DirectedFlowCutGap.MeasuredBudgetPrices
import DirectedFlowCutGap.MeasuredSparsityScore
import DirectedFlowCutGap.ConcurrentEdgeBudgetWidths

/-! Generate the original geometric budget entries by binary division,
Euclidean normalization and powers of two. -/
namespace DirectedFlowCutGap.MeasuredDoublingBudgetGrid

open scoped NNRat
open RawNonnegativeRational (Code)
open MeasuredBudgetPrices (canonical canonicalWork)

private theorem budget_mono {B C : ℕ} (h : B ≤ C) :
    BinaryRawRational.budget B ≤ BinaryRawRational.budget C := by
  unfold BinaryRawRational.budget
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 3) 2)

def rangeCount (lo hi : Code) : ℕ × ℕ :=
  let ratio := BinaryRawRational.div hi lo
  let reduced := canonical ratio.1
  (reduced.1.num.length,ratio.2+reduced.2)

theorem rangeCount_value (lo hi : Code) : (rangeCount lo hi).1 = ConcurrentEdgeBudgetGrid.gridSteps lo.value hi.value := by
  simp only [rangeCount,MeasuredBudgetPrices.canonical_value,BinaryRawRational.div_value,Code.value_div,
    BinaryRawRational.encode_eq,BinaryRationalCeiling.ofCode,Code.ofNNRat,
    ConcurrentEdgeBudgetGrid.gridSteps,Nat.size_eq_bits_len]

def rangeWork (L H : ℕ) : ℕ := BinaryRawRational.budget (max L H)+canonicalWork (L+H)

theorem rangeCount_charge (lo hi : Code) {L H : ℕ} (low : lo.Bounded L) (high : hi.Bounded H) :
    (rangeCount lo hi).2 ≤ rangeWork L H := by
  let result := BinaryRawRational.div hi lo
  have width : result.1.Bounded (L+H) := by
    change (BinaryRawRational.div hi lo).1.Bounded (L+H)
    rw [BinaryRawRational.div_value,Nat.add_comm]
    exact Code.bounded_div high low
  exact Nat.add_le_add
    (BinaryRawRational.div_paid (Code.bounded_mono high (le_max_right L H)) (Code.bounded_mono low (le_max_left L H)))
    (MeasuredBudgetPrices.canonical_bounds width).2

def item (lo : Code) (k : ℕ) : Code × ℕ :=
  let scale := MeasuredSparsityScore.power (Code.ofNat 2) k
  let result := BinaryRawRational.mul lo scale.1
  (result.1,scale.2+result.2)

theorem item_value (lo : Code) (k : ℕ) : (item lo k).1.value = lo.value*(2 : ℚ≥0)^k := by
  simp only [item,BinaryRawRational.mul_value,Code.value_mul,MeasuredSparsityScore.power_value,
    Code.value_ofNat,Nat.cast_ofNat]

def itemWork (L J : ℕ) : ℕ := J*BinaryRawRational.budget J+BinaryRawRational.budget (max L J)

theorem item_bounds (lo : Code) (k : ℕ) {L J : ℕ} (fit : lo.Bounded L) (steps : k ≤ J) (positive : 1 ≤ J) :
    (item lo k).1.Bounded (L+k) ∧ (item lo k).2 ≤ itemWork L J := by
  have two : (Code.ofNat 2).Bounded 1 := MeasuredMultiplicityUpdate.ofNat_fits (by decide)
  have powered := MeasuredSparsityScore.power_fits (Code.ofNat 2) two k
  have bits : (MeasuredSparsityScore.power (Code.ofNat 2) k).1.Bounded k := by
    simpa only [Nat.mul_one] using powered
  have prior := MeasuredSparsityScore.power_charge (Code.ofNat 2) two k
  rw [Nat.mul_one] at prior
  have powFees := prior.trans (Nat.mul_le_mul steps (budget_mono (max_le positive steps)))
  have mult := BinaryRawRational.mul_paid (Code.bounded_mono fit (le_max_left L J))
    (Code.bounded_mono bits (steps.trans (le_max_right L J)))
  exact ⟨by simpa only [item,BinaryRawRational.mul_value] using Code.bounded_mul fit bits,
    Nat.add_le_add powFees mult⟩

def grid (lo hi : Code) : List Code × ℕ :=
  let count := rangeCount lo hi
  let entries := (List.range (count.1+2)).map (item lo)
  (entries.map Prod.fst,count.2+(entries.map Prod.snd).sum)

theorem grid_value (lo hi : Code) :
    (grid lo hi).1.map Code.value = ConcurrentEdgeBudgetGrid.grid lo.value hi.value := by
  simp only [grid,List.map_map,Function.comp_def,rangeCount_value,ConcurrentEdgeBudgetGrid.grid,item_value]

theorem rangeCount_le (lo hi : Code) {L H : ℕ} (low : lo.Bounded L) (high : hi.Bounded H) :
    (rangeCount lo hi).1 ≤ L+H+1 := by
  simpa only [rangeCount_value] using ConcurrentEdgeBudgetWidths.steps_le lo.value hi.value
    (NNRatStoredBounds.value_bounded low) (NNRatStoredBounds.value_bounded high)

theorem grid_field (lo hi : Code) {L H : ℕ} (low : lo.Bounded L) (high : hi.Bounded H)
    {entry : Code} (present : entry ∈ (grid lo hi).1) : entry.Bounded (2*L+H+2) := by
  simp only [grid,List.map_map,Function.comp_def,List.mem_map] at present
  obtain ⟨k,member,rfl⟩ := present
  have active := List.mem_range.mp member
  have steps := rangeCount_le lo hi low high
  have limit : k ≤ L+H+2 := by omega
  exact Code.bounded_mono (item_bounds lo k low limit (by omega)).1 (by omega)

private theorem bounded_sum {α : Type*} (xs : List α) (f : α → ℕ) {B : ℕ}
    (fit : ∀ q ∈ xs, f q ≤ B) : (xs.map f).sum ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have pair := Nat.add_le_add (fit a List.mem_cons_self) (ih (fun q hq => fit q (List.mem_cons_of_mem _ hq)))
    simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm] using pair

def gridWork (L H : ℕ) : ℕ := rangeWork L H+(L+H+3)*itemWork L (L+H+2)

theorem grid_charge (lo hi : Code) {L H : ℕ} (low : lo.Bounded L) (high : hi.Bounded H) :
    (grid lo hi).2 ≤ gridWork L H := by
  let steps := (rangeCount lo hi).1
  have maxSteps : steps ≤ L+H+1 := rangeCount_le lo hi low high
  have each (k : ℕ) (member : k ∈ List.range (steps+2)) : (item lo k).2 ≤ itemWork L (L+H+2) := by
    have active := List.mem_range.mp member
    exact (item_bounds lo k low (by omega) (by omega)).2
  have spent := bounded_sum (List.range (steps+2)) (fun k => (item lo k).2) each
  rw [List.length_range] at spent
  have enough : steps+2 ≤ L+H+3 := by omega
  simpa only [grid,gridWork,List.map_map,Function.comp_def,steps] using
    Nat.add_le_add (rangeCount_charge lo hi low high) (spent.trans (Nat.mul_le_mul_right _ enough))

end DirectedFlowCutGap.MeasuredDoublingBudgetGrid
