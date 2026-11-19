import DirectedFlowCutGap.PhysicalCoverWidthEnvelope
import DirectedFlowCutGap.PhysicalVertexRounding
import DirectedFlowCutGap.ChargedVertexModes

/-! Bound the rational fields of the actual heavy-vertex, port, clone and
uniform-chain preparations. Bounds use numerator and denominator fields. -/

namespace DirectedFlowCutGap.VertexReductionWidths

open RawNonnegativeRational EncodedUnitCostReplication
open BinaryFractionalRows BinaryRational

structure InputFits {n : ℕ} (D : Input n) (b : ℕ) : Prop where
  weights : ∀ i : Fin n, D.weights[i.val].Bounded b
  costs : ∀ i : Fin n, D.costs[i.val].Bounded b

theorem input_mono {n a b : ℕ} {D : Input n} (fits : InputFits D a) (h : a ≤ b) : InputFits D b :=
  ⟨fun i => Code.bounded_mono (fits.weights i) h,fun i => Code.bounded_mono (fits.costs i) h⟩

theorem fractional_input {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    {rows : List (FractionalCoverRawCore.RawRow n)} {row : FractionalCoverRawCore.RawRow n}
    (stored : PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput D).1 = .covers rows)
    (member : row ∈ rows) :
    InputFits (EncodedVertexSolver.roundingInput (BinaryFractionalGuesses.decodeInput D) row)
      (max (ChargedVertexModes.priceWidth D)
        (1+PhysicalSourceDispatch.instructionPolynomial.eval (PhysicalSourceDispatch.input D).length)) := by
  constructor
  · intro i
    exact Code.bounded_mono (PhysicalCoverWidthEnvelope.rows_width D rows stored row member i) (le_max_right _ _)
  · intro i
    change (FractionalCoverRawCore.get (decodeRow D.costs) i).Bounded _
    rw [decode_get]
    exact Code.bounded_mono (stored_raw_bound (ChargedVertexModes.priceWidth_bounds D i)) (le_max_left _ _)

section Heavy

open EncodedHeavyVertexPreparation EncodedCubeRootThreshold

theorem heavy_fields {n b : ℕ} (D : Input n) (fits : InputFits D b) :
    InputFits (prepare D).1.data (b+1) := by
  refine ⟨build_weights_bounded D (threshold n) b fits.weights,?_⟩
  intro i
  exact Code.bounded_mono (build_costs_bounded D (threshold n) b fits.costs i) (Nat.le_succ b)

theorem heavy_comparisons {n b : ℕ} (D : Input n) (fits : InputFits D b) (i : Fin n) :
    Nat.size (D.weights[i.val].num*(threshold n).den) ≤ b+4*(n+1)+1 ∧
      Nat.size ((threshold n).num*D.weights[i.val].den) ≤ b+4*(n+1)+1 := by
  have size : (4*ceilCube n).size ≤ 4*(n+1) :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.mul_le_mul_left 4 (ceilCube_upper n))
  have h := Code.comparison_intermediates (fits.weights i)
    (Code.bounded_mono (threshold_bounded n) size)
  exact ⟨(Nat.size_le_size h.1).trans_eq Nat.size_pow,(Nat.size_le_size h.2).trans_eq Nat.size_pow⟩

end Heavy

section Port

open EncodedUnitCostPreparation EncodedPortPreparation

theorem prepared_fields {n b : ℕ} (D : Input n) (fits : InputFits D b) : InputFits (build D).data (b+1) :=
  ⟨build_weight_bounded D b fits.weights,fun i => Code.bounded_mono (build_cost_bounded D b fits.costs i) (Nat.le_succ b)⟩

def normalizationWidth (n b : ℕ) : ℕ := 3*n*(3*b+5)+b+2

theorem normalization_fields {n b : ℕ} (D : Input n) (fits : InputFits D b) (i : Fin (build D).size) :
    ((build D).data.normalized (build D).data.totals)[i.val].Bounded (normalizationWidth n b) := by
  have stored := prepared_fields D fits
  apply Code.bounded_mono ((build D).data.normalized_bounded (b+1) stored.weights stored.costs i)
  have dim := Nat.mul_le_mul_right (3*b+5) (build_size_le D)
  unfold normalizationWidth
  nlinarith

theorem normalization_ceiling {n b : ℕ} (D : Input n) (fits : InputFits D b) (i : Fin (build D).size) :
    let value := ((build D).data.normalized (build D).data.totals)[i.val]
    (value.num+value.den).size ≤ normalizationWidth n b+2 := by
  have h := Code.ceiling_intermediate (normalization_fields D fits i)
  exact (Nat.size_le_size h).trans_eq Nat.size_pow

theorem replica_fields {n b : ℕ} (D : Input n) (fits : InputFits D b) :
    let p := build D
    InputFits (materialize p.data p.data.counts).input (b+1) := by
  let p := build D
  have keep := prepared_fields D fits
  constructor
  · intro i
    change (materialize p.data p.data.counts).weights[i.val].Bounded _
    rw [materialize_weight]
    exact keep.weights _
  · intro i
    change (materialize p.data p.data.counts).costs[i.val].Bounded _
    rw [materialize_cost]
    exact Code.bounded_mono Code.bounded_one (Nat.zero_le _)

theorem low_comparisons {n b : ℕ} (D : Input n) (fits : InputFits D b) (i : Fin n) :
    let q := Code.one.div (Code.ofNat (2*n))
    Nat.size (D.weights[i.val].num*q.den) ≤ b+2*n+1 ∧
      Nat.size (q.num*D.weights[i.val].den) ≤ b+2*n+1 := by
  have h := Code.comparison_intermediates (fits.weights i)
    (Code.bounded_mono (lowThreshold_bounded n) (Nat.size_le.mpr Nat.lt_two_pow_self))
  exact ⟨(Nat.size_le_size h.1).trans_eq Nat.size_pow,(Nat.size_le_size h.2).trans_eq Nat.size_pow⟩

end Port

section Uniform

open EncodedUniformWeightParameters

def uniformWidth {R : Type*} [Semiring R] (n b : R) : R := b+3*n*(b+1)+3*n

theorem uniform_fields {n b : ℕ} (D : Input n) (fits : InputFits D b) :
    (compute D).total.Bounded (uniformWidth n b) ∧ (compute D).average.Bounded (uniformWidth n b) ∧
    ∀ i : Fin (3*n), (compute D).ratios[i.val].Bounded (uniformWidth n b) := by
  have s : (3*n).size ≤ 3*n := Nat.size_le.mpr Nat.lt_two_pow_self
  refine ⟨Code.bounded_mono (total_bounded D b fits.weights) (by unfold uniformWidth; omega),
    Code.bounded_mono (average_bounded D b fits.weights) (by unfold uniformWidth; omega),?_⟩
  intro i
  exact Code.bounded_mono (ratios_bounded D b fits.weights i) (by unfold uniformWidth; omega)

theorem uniform_ceiling {n b : ℕ} (D : Input n) (fits : InputFits D b) :
    let q := Code.one.div (compute D).average
    (q.num+q.den).size ≤ uniformWidth n b+2 ∧
    ∀ i : Fin (3*n), ((compute D).ratios[i.val].num+(compute D).ratios[i.val].den).size ≤ uniformWidth n b+2 := by
  obtain ⟨_,avg,ratios⟩ := uniform_fields D fits
  have h : (Code.one.div (compute D).average).Bounded (uniformWidth n b) := by
    simpa only [Nat.zero_add] using Code.bounded_div Code.bounded_one avg
  exact ⟨(Nat.size_le_size (Code.ceiling_intermediate h)).trans_eq Nat.size_pow,
    fun i => (Nat.size_le_size (Code.ceiling_intermediate (ratios i))).trans_eq Nat.size_pow⟩

theorem replica_uniform_width {n b : ℕ} (D : Input n) (fits : InputFits D b) (positive : 0<n)
    (objective : (EncodedUnitCostPreparation.build D).data.totals.objective.num ≠ 0) :
    let p := EncodedUnitCostPreparation.build D
    let r := materialize p.data p.data.counts
    let params := compute r.input
    params.total.Bounded (uniformWidth (4*n^2) (b+1)) ∧ params.average.Bounded (uniformWidth (4*n^2) (b+1)) ∧
      ∀ i : Fin (3*(cloneList p.data.counts).length), params.ratios[i.val].Bounded (uniformWidth (4*n^2) (b+1)) := by
  let p := EncodedUnitCostPreparation.build D
  let r := materialize p.data p.data.counts
  obtain ⟨ht,ha,hr⟩ := uniform_fields r.input (replica_fields D fits)
  have size := EncodedUnitCostPreparation.build_clone_count D positive objective
  have width : uniformWidth (cloneList p.data.counts).length (b+1) ≤ uniformWidth (4*n^2) (b+1) := by
    unfold uniformWidth
    gcongr
  exact ⟨Code.bounded_mono ht width,Code.bounded_mono ha width,fun i => Code.bounded_mono (hr i) width⟩

end Uniform

end DirectedFlowCutGap.VertexReductionWidths
