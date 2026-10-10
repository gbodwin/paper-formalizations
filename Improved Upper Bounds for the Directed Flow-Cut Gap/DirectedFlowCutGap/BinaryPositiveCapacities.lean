import DirectedFlowCutGap.BinaryFractionalRows
import DirectedFlowCutGap.ZeroWeights

/-!
# Positive auxiliary capacities with unchanged selected amounts

The covering recurrence needs positive capacities at every coordinate. This
charged binary scan replaces precisely the original zero coordinates by one.
The original graph weights, threshold demands and total W are separate inputs
and are never replaced by this auxiliary row. A zero-avoiding final cut selects
only entries whose full original numerator/denominator bit words are preserved.

The auxiliary potential may stop at a different time from the original one.
Only its inequality with the original potential is used; no equality of the
stopping conditions is claimed. The chosen bottleneck must be recomputed from
the final selected cut before the controller creates its retained event.
-/
namespace DirectedFlowCutGap.BinaryPositiveCapacities

open scoped BigOperators NNRat
open BinaryRational BinaryFractionalRows EncodedRoundingInput

variable {m : ℕ}

def prepare (w : Row m) : Row m × ℕ :=
  tabulate fun i : Fin m =>
    let z := BinaryRational.isZero (get w i)
    (if z.1 then BinaryRational.one else get w i, z.2 + 6)

@[simp] theorem prepare_get (w : Row m) (i : Fin m) :
    get (prepare w).1 i =
      if (BinaryRational.isZero (get w i)).1 then BinaryRational.one else get w i := by
  simp [prepare, BinaryFractionalRows.get, tabulate_value]

theorem preserves_positive (w : Row m) (i : Fin m)
    (hi : 0 < (decode (get w i)).value) : get (prepare w).1 i = get w i := by
  have hn : (decode (get w i)).num ≠ 0 :=
    Nat.ne_of_gt ((RawNonnegativeRational.Code.value_pos _).mp hi)
  have hz : (BinaryRational.isZero (get w i)).1 = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact hn ((BinaryRational.isZero_decode _).mp h)
  simp [prepare_get, hz]

theorem positive (w : Row m) (i : Fin m) :
    0 < (decode (get (prepare w).1 i)).value := by
  rw [prepare_get]
  cases hz : (BinaryRational.isZero (get w i)).1 with
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      apply (RawNonnegativeRational.Code.value_pos _).mpr
      apply Nat.pos_of_ne_zero
      intro hn
      have h := (BinaryRational.isZero_decode (get w i)).mpr hn
      simp [hz] at h
  | true => simp

theorem original_le (w : Row m) (i : Fin m) :
    (decode (get w i)).value ≤ (decode (get (prepare w).1 i)).value := by
  rw [prepare_get]
  cases hz : (BinaryRational.isZero (get w i)).1 with
  | false => simp
  | true =>
      have hn := (BinaryRational.isZero_decode (get w i)).mp hz
      simp [RawNonnegativeRational.Code.value, hn]

def value (w : Row m) (i : Fin m) : ℝ := ((decode (get w i)).value : ℝ)

theorem potential_le (w : Row m) (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) :
    mwPotential (value w) c ≤ mwPotential (value (prepare w).1) c := by
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left ?_ (hc i)
  change ((decode (get w i)).value : ℝ) ≤ ((decode (get (prepare w).1 i)).value : ℝ)
  exact_mod_cast original_le w i

/-- Use this only after the original-weight oracle inequality has been proved. -/
theorem weaken_budget (w : Row m) (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i)
    (α : ℝ) (hα : 0 ≤ α) (cost : ℝ)
    (hcost : cost ≤ α * mwPotential (value w) c) :
    cost ≤ α * mwPotential (value (prepare w).1) c :=
  hcost.trans (mul_le_mul_of_nonneg_left (potential_le w c hc) hα)

/-- Every selected entry retains its exact original encoding, including padding.
Consequently the final selected bottleneck's retained amount is unchanged. -/
theorem selected_entries (w : Row m) (mask : Vector Bool m)
    (h : ∀ i : Fin m, mask[i.val] = true → 0 < (decode (get w i)).value) :
    ∀ i : Fin m, mask[i.val] = true → get (prepare w).1 i = get w i := by
  intro i hi
  exact preserves_positive w i (h i hi)

theorem stored (w : Row m) (B : ℕ)
    (hw : ∀ i, StoredBounded (get w i) B) :
    ∀ i, StoredBounded (get (prepare w).1 i) (B+1) := by
  intro i
  rw [prepare_get]
  split
  · simp [StoredBounded, BinaryRational.one]
  · exact ⟨(hw i).1.trans (Nat.le_succ B), (hw i).2.trans (Nat.le_succ B)⟩

theorem charge (w : Row m) (B : ℕ)
    (hw : ∀ i, StoredBounded (get w i) B) :
    (prepare w).2 ≤ m * (4*(B+1)+6) + arrayBound m := by
  apply tabulate_bound
  intro i
  exact Nat.add_le_add_right (BinaryRational.isZero_charge (hw i)) 6

end DirectedFlowCutGap.BinaryPositiveCapacities
