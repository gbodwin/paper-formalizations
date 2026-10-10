import DirectedFlowCutGap.BinaryWeightedPacking
import DirectedFlowCutGap.WeightedBitConfidence

/-!
# Computed fuel for the final original-weight draw

This companion supplies the final sampler half of the existing failure split
using an actual Boolean-list program. Its numerical fuel is `2*B+m+3`, not
merely a word of bounded stored length. The wrapper charges fuel preparation
once and retains every controller and sampler field unchanged.

The same-query graph-provider error bound and the oracle half of the split
remain explicit premises. This does not instantiate that provider, its inner
randomness budget, the finite-code simulation, or the whole-paper runtime.
-/
namespace DirectedFlowCutGap.BinaryWeightedPackingConfidence

open BinaryArithmetic BinaryFractionalRows BinaryRational
open scoped ENNReal

variable {m : ℕ}

/-- Exactly one final bounded-rejection draw is budgeted here. -/
def fuel (resources width : Bits) : Bits × ℕ :=
  WeightedBitConfidence.prepare [true] resources width

theorem fuel_value (resources width : Bits) :
    value (fuel resources width).1 = 2*value width+value resources+3 := by
  have h := WeightedBitConfidence.prepare_value [true] resources width
  change value (WeightedBitConfidence.prepare [true] resources width).1 = _
  simp only [WeightedBitConfidence.trialCount,value,Bool.toNat_true] at h
  omega

theorem fuel_length (resources width : Bits) (K : ℕ) (hK : 1 ≤ K)
    (hm : resources.length ≤ K) (hB : width.length ≤ K) :
    (fuel resources width).1.length ≤ K+4 := by
  exact WeightedBitConfidence.prepare_length [true] resources width K
    (by simpa using hK) hm hB

theorem fuel_charge (resources width : Bits) (K : ℕ) (hK : 1 ≤ K)
    (hm : resources.length ≤ K) (hB : width.length ≤ K) :
    (fuel resources width).2 ≤ 64*(K+4) := by
  exact WeightedBitConfidence.prepare_charge [true] resources width K
    (by simpa using hK) hm hB

theorem fuel_failure (resources width : Bits) :
    ((1 : ℝ)/2)^value (fuel resources width).1 ≤
      WeightedFailureBudget.tolerance (value resources) (value width)/2 := by
  simpa [fuel,value] using
    WeightedBitConfidence.prepared_failure [true] resources width

/-- Only the total operation annotation changes; all physical history and
sampler fields of the original output remain exactly those returned. -/
def account {w : Row m} {columns : Set (FractionalCover.Column m)}
    (preparation : ℕ) (out : BinaryWeightedPacking.Output w columns) : BinaryWeightedPacking.Output w columns :=
  {out with operations := preparation+out.operations+4}

/-- One fuel preparation, then the actual retained packing/sampling program. -/
def run {M : Type → Type} [Monad M] (w : Row m)
    (columns : Set (FractionalCover.Column m))
    (hS : BinaryZeroAvoidingProvider.SupportValid w columns)
    (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : BinaryZeroAvoidingProvider.CutProvider M columns) (bit : M Bool)
    (resources width : Bits) : M (BinaryWeightedPacking.Output w columns) := do
  let prepared := fuel resources width
  let out ← BinaryWeightedPacking.run w columns hS hempty draw bit prepared.1
  pure (account prepared.2 out)

noncomputable section

theorem run_eq_map (w : Row m) (columns : Set (FractionalCover.Column m))
    (hS : BinaryZeroAvoidingProvider.SupportValid w columns)
    (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : BinaryZeroAvoidingProvider.CutProvider PMF columns) (resources width : Bits) :
    run w columns hS hempty draw BinaryWeightedSamplingLaw.fairBit resources width =
      (BinaryWeightedPacking.run w columns hS hempty draw BinaryWeightedSamplingLaw.fairBit
        (fuel resources width).1).map (account (fuel resources width).2) := by
  rfl

/-- This is the original exact-W factor-four conclusion with its final sampler
fuel now constructed internally. The remaining provider premise is unchanged. -/
theorem run_marginal_four (w : Row m) (columns : Set (FractionalCover.Column m))
    (hS : BinaryZeroAvoidingProvider.SupportValid w columns)
    (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : BinaryZeroAvoidingProvider.CutProvider PMF columns) (hm : 0 < m) (B : ℕ)
    (hwidth : ∀ i, (decode (get w i)).Bounded B)
    {α ε : ℝ} (hα : 0 < α) (hε : 0 ≤ ε)
    (hunit : 1 ≤ α*WeightedFailureBudget.totalWeight (fun i => decode (get w i)))
    (hcharged : ∀ c, (draw (BinaryZeroAvoidingSelector.prepare w c).costs).toOuterMeasure
      (BinaryZeroAvoidingProbability.chargedFailure w c α) ≤ ENNReal.ofReal ε)
    (resources width : Bits) (hresources : value resources=m) (hwidthValue : value width=B)
    (horacle : (3*m^2+1 : ℕ)*ε ≤ WeightedFailureBudget.tolerance m B/2)
    (i : Fin m) :
    ((run w columns hS hempty draw BinaryWeightedSamplingLaw.fairBit resources width).toOuterMeasure {out | out.selected.label.any
        (BinaryApproximatePackingSampling.coordinate i) = true}).toReal ≤
      4*α*(FractionalCover.value (BinaryApproximatePacking.capacities w) i : ℝ) := by
  have hf := fuel_failure resources width
  rw [hresources,hwidthValue] at hf
  rw [run_eq_map,PMF.toOuterMeasure_map_apply]
  change ((BinaryWeightedPacking.run w columns hS hempty draw BinaryWeightedSamplingLaw.fairBit
    (fuel resources width).1).toOuterMeasure {out | out.selected.label.any
      (BinaryApproximatePackingSampling.coordinate i) = true}).toReal ≤ _
  exact BinaryWeightedPacking.run_marginal_four w columns hS hempty draw hm B hwidth hα hε hunit
    hcharged (fuel resources width).1 horacle hf i

end
end DirectedFlowCutGap.BinaryWeightedPackingConfidence


/-! Proof-only consequence of the actual per-query failure bound.
No executable query or body is added or changed. -/
namespace DirectedFlowCutGap.BinaryWeightedPackingConfidence
open scoped BigOperators ENNReal
open BinaryFractionalRows BinaryRational BinaryApproximatePacking
open BinaryApproximatePackingZeros BinaryZeroAvoidingSelector
open BinaryZeroAvoidingProvider BinaryZeroAvoidingProbability

noncomputable section
variable {m : ℕ}

/-- A proof-side unit-cost query used to derive a necessary factor bound. -/
def unitCostRow (m : ℕ) : Row m := Vector.replicate m BinaryRational.one

@[simp] theorem unitCostRow_value (i : Fin m) :
    tableValue (unitCostRow m) i = 1 := by
  simp [unitCostRow,tableValue_apply,BinaryFractionalRows.get]

theorem unitCostRow_potential (w : Row m) :
    mwPotential (tableValue w) (tableValue (unitCostRow m)) =
      WeightedFailureBudget.totalWeight (fun i => decode (get w i)) := by
  unfold mwPotential WeightedFailureBudget.totalWeight
  apply Finset.sum_congr rfl
  intro i _
  rw [unitCostRow_value,one_mul,tableValue_apply,WeightedFailureBudget.weight_eq_value]

theorem unitCostRow_answerCost (a : Answer m) :
    answerCost (unitCostRow m) a =
      ((BinaryFractionalCore.decodeChoice a.choice).column.card : ℝ) := by
  simp only [answerCost,unitCostRow_value]
  simp

/-- No unit-mass assumption is needed: a failure bound strictly below one at
this actual penalized unit query forces it. Every provider return is nonempty,
including fallback returns and answers with the physical failure flag set. -/
theorem unit_mass_of_charged_failure (w : Row m)
    (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns) (α ε : ℝ) (hε : ε < 1)
    (hcharged : (draw (prepare w (unitCostRow m)).costs).toOuterMeasure
      (chargedFailure w (unitCostRow m) α) ≤ ENNReal.ofReal ε) :
    1 ≤ α * WeightedFailureBudget.totalWeight (fun i => decode (get w i)) := by
  have hb := (provider_failure_le_charged w (unitCostRow m)
    columns hS hempty draw α).trans hcharged
  by_contra h
  have ht := lt_of_not_ge h
  have hall : (provider w columns hS hempty draw (unitCostRow m)).toOuterMeasure
      {a | a.1 ∈ outputFailure w (unitCostRow m) α} = 1 := by
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).2
    intro a _
    have hn : (BinaryFractionalCore.decodeChoice a.1.choice).column.Nonempty :=
      ⟨a.1.choice.bottleneck,a.2.2.1⟩
    have hc : (1 : ℝ) ≤ (BinaryFractionalCore.decodeChoice a.1.choice).column.card := by
      exact_mod_cast Finset.card_pos.mpr hn
    change α * mwPotential (tableValue w) (tableValue (unitCostRow m)) <
      answerCost (unitCostRow m) a.1
    rw [unitCostRow_potential,unitCostRow_answerCost]
    exact ht.trans_le hc
  rw [hall] at hb
  exact (not_le_of_gt (ENNReal.ofReal_lt_one.mpr hε)) hb

/-- The already required oracle half-budget is strictly below one. -/
theorem oracle_error_lt_one (m B : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hbudget : (3*m^2+1 : ℕ)*ε ≤ WeightedFailureBudget.tolerance m B/2) : ε < 1 := by
  have hp : (1 : ℝ) ≤ (2 : ℝ)^WeightedFailureBudget.exponent m B :=
    one_le_pow₀ (by norm_num)
  have ht : WeightedFailureBudget.tolerance m B ≤ 1 := by
    unfold WeightedFailureBudget.tolerance
    exact (div_le_one (by positivity)).2 hp
  have hf : (1 : ℝ) ≤ (3*m^2+1 : ℕ) := by
    exact_mod_cast (by omega : 1 ≤ 3*m^2+1)
  have he := (le_mul_of_one_le_left hε hf).trans hbudget
  linarith

/-- Factor four for the actual original-weight output, with the old unit-mass
premise discharged by the already assumed same-query failure contract. -/
theorem run_marginal_four_of_charged_failure (w : Row m)
    (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns) (hm : 0 < m) (B : ℕ)
    (hwidth : ∀ i, (decode (get w i)).Bounded B)
    {α ε : ℝ} (hα : 0 < α) (hε : 0 ≤ ε)
    (hcharged : ∀ c, (draw (prepare w c).costs).toOuterMeasure
      (chargedFailure w c α) ≤ ENNReal.ofReal ε)
    (resources width : BinaryArithmetic.Bits)
    (hresources : BinaryArithmetic.value resources=m)
    (hwidthValue : BinaryArithmetic.value width=B)
    (horacle : (3*m^2+1 : ℕ)*ε ≤ WeightedFailureBudget.tolerance m B/2)
    (i : Fin m) :
    ((run w columns hS hempty draw BinaryWeightedSamplingLaw.fairBit resources width).toOuterMeasure {out | out.selected.label.any
        (BinaryApproximatePackingSampling.coordinate i) = true}).toReal ≤
      4*α*(FractionalCover.value (BinaryApproximatePacking.capacities w) i : ℝ) := by
  have hu := unit_mass_of_charged_failure w columns hS hempty draw α ε
    (oracle_error_lt_one m B hε horacle) (hcharged (unitCostRow m))
  exact run_marginal_four w columns hS hempty draw hm B hwidth hα hε hu
    hcharged resources width hresources hwidthValue horacle i

end
end DirectedFlowCutGap.BinaryWeightedPackingConfidence
