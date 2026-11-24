import DirectedFlowCutGap.NormalizedOptimalSparsity
import DirectedFlowCutGap.RationalEdgeDecomposition

/-! Choose the smaller sparsity scale using a rational comparison.
The implementation does not evaluate real powers or use an unknown constant. -/
namespace DirectedFlowCutGap.NormalizedOptimalMode

open scoped BigOperators NNReal NNRat ENNReal
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalSparsestEdgeThreshold (actualDistance choose)
open RationalSparsestEdgeRound (Result Mask scaled tapeBudget drawBound demandSet)
open RationalSparsestEdgeExpectation (normalizedMass)
open FiniteHarmonicThreshold (harmonicWeight)

def harmonic (m : ℕ) : ℚ≥0 := ∑ j : Fin m, 1 / ((j.val + 1 : ℕ) : ℚ≥0)

theorem harmonic_eq (m : ℕ) : (harmonic m : ℝ≥0) = harmonicWeight m := by
  simp only [harmonic, harmonicWeight, NNRat.cast_sum, NNRat.cast_div, NNRat.cast_one, NNRat.cast_natCast]

def averageMass {m n : ℕ} (A : Adjacency n) (w : Weights n)
    (pairs : Vector (Fin n × Fin n) m) : ℚ≥0 :=
  (m : ℚ≥0) * RationalEdgeDecomposition.originalTotal A w /
    ∑ j : Fin m, (RationalSparsestEdgeDistances.distance A w pairs[j.val]).getD 0

theorem averageMass_eq {m n : ℕ} (A : Adjacency n) (w : Weights n)
    (pairs : Vector (Fin n × Fin n) m) : (averageMass A w pairs : ℝ≥0) = normalizedMass A w pairs := by
  have total : (RationalEdgeDecomposition.originalTotal A w : ℝ≥0) =
      totalEdgeWeight (graph A) (weights w) := by
    simp only [RationalEdgeDecomposition.originalTotal, NNRat.cast_sum,
      RationalEdgeDecomposition.originalWeight_eq]
    exact_mod_cast WeakDecomposition.sum_actualEdgeWeight (graph A) (weights w)
  have distance (j : Fin m) :
      (((RationalSparsestEdgeDistances.distance A w pairs[j.val]).getD 0 : ℚ≥0) : ℝ≥0) =
        actualDistance A w pairs j := by
    cases found : RationalSparsestEdgeDistances.distance A w pairs[j.val] with
    | some d => exact RationalSparsestEdgeDistances.finite_value A w pairs[j.val] found
    | none =>
      have unreachable := (RationalSparsestEdgeDistances.none_iff A w pairs[j.val]).mp found
      simp only [actualDistance, SparsestEdgeBridge.demandDistance, unreachable, ENNReal.toNNReal_top,
        Option.getD_none, NNRat.cast_zero]
  simp only [averageMass, normalizedMass, NNRat.cast_div, NNRat.cast_mul, NNRat.cast_natCast,
    NNRat.cast_sum, total, distance]

def pick {m n : ℕ} (A : Adjacency n) (w : Weights n)
    (pairs : Vector (Fin n × Fin n) m) : ChargedVertexModes.Mode :=
  if (harmonic m * averageMass A w pairs)^3 ≤ (n : ℚ≥0)^2 then .mass else .size

noncomputable def sizeScale (n m : ℕ) : ℝ :=
  (n : ℝ)^(1/3 : ℝ) * (harmonicWeight m : ℝ)

noncomputable def massScale (m : ℕ) (W : ℝ≥0) : ℝ :=
  (harmonicWeight m : ℝ)^(3/2 : ℝ) * (W : ℝ)^(1/2 : ℝ)

theorem pick_minimum {m n : ℕ} (A : Adjacency n) (w : Weights n)
    (pairs : Vector (Fin n × Fin n) m) :
    let W := normalizedMass A w pairs
    match pick A w pairs with
    | .mass => massScale m W ≤ sizeScale n m
    | .size => sizeScale n m ≤ massScale m W := by
  let H : ℝ := harmonicWeight m
  let W : ℝ := normalizedMass A w pairs
  let x := (n : ℝ)^(1/3 : ℝ)
  let y := (H*W)^(1/2 : ℝ)
  have nx : 0 ≤ x := Real.rpow_nonneg (by positivity) _
  have ny : 0 ≤ y := Real.rpow_nonneg (by positivity) _
  have x6 : x^6 = (n : ℝ)^2 := by
    rw [show x = (n : ℝ)^(1/3 : ℝ) from rfl, ← Real.rpow_mul_natCast (by positivity)]
    norm_num [Real.rpow_natCast]
  have y6 : y^6 = (H*W)^3 := by
    rw [show y = (H*W)^(1/2 : ℝ) from rfl, ← Real.rpow_mul_natCast (by positivity)]
    norm_num [Real.rpow_natCast]
  have size : sizeScale n m = x * H := rfl
  have mass : massScale m (normalizedMass A w pairs) = y * H := by
    unfold massScale y
    change H^(3/2 : ℝ)*W^(1/2 : ℝ) = (H*W)^(1/2 : ℝ)*H
    rw [Real.mul_rpow (by positivity : 0 ≤ H) (by positivity : 0 ≤ W)]
    have times : H^(3/2 : ℝ) = H^(1/2 : ℝ)*H := calc
      _ = H^(1/2 : ℝ)*H^(1 : ℝ) := by
        rw [← Real.rpow_add_of_nonneg (by positivity : 0 ≤ H) (by norm_num : 0 ≤ (1/2 : ℝ))
          (by norm_num : 0 ≤ (1 : ℝ))]
        norm_num
      _ = _ := by rw [Real.rpow_one]
    rw [times]
    ring
  have comparison : (harmonic m * averageMass A w pairs)^3 ≤ (n : ℚ≥0)^2 ↔
      (H*W)^3 ≤ (n : ℝ)^2 := calc
    _ ↔ (((harmonic m * averageMass A w pairs)^3 : ℚ≥0) : ℝ≥0) ≤
        (((n : ℚ≥0)^2 : ℚ≥0) : ℝ≥0) := (NNRat.cast_le (K := ℝ≥0)).symm
    _ ↔ _ := by
      simp only [← NNReal.coe_le_coe, NNRat.cast_pow, NNRat.cast_mul, NNRat.cast_natCast,
        harmonic_eq, averageMass_eq, NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_natCast, H, W]
  by_cases lower : (harmonic m * averageMass A w pairs)^3 ≤ (n : ℚ≥0)^2
  · simp only [pick, ite_eq_left lower]
    rw [size, mass]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (pow_le_pow_iff_left₀ ny nx (by decide : 6 ≠ 0)).mp
      (by rw [y6,x6]; exact comparison.mp lower)
  · simp only [pick, ite_eq_right lower]
    rw [size, mass]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (pow_le_pow_iff_left₀ nx ny (by decide : 6 ≠ 0)).mp
      (by rw [x6,y6]; exact le_of_lt (lt_of_not_ge (mt comparison.mpr lower)))

def runBest {m n : ℕ} (A : Adjacency n) (c : Weights n)
    (pairs : Vector (Fin n × Fin n) m) (T : ℕ) (tape : Bits) : Option (ℚ × Result n) :=
  (NormalizedEdgeLP.minimize A c pairs.get (m : ℚ≥0)).bind fun (q,w) =>
    (RationalSparsestEdgeRound.run A w c pairs (pick A w pairs) T tape).map fun result => (q,result)

theorem selected_run {m n : ℕ} (A : Adjacency n) (c : Weights n)
    (pairs : Vector (Fin n × Fin n) m) (T : ℕ) (tape : Bits) {q : ℚ} {w : Weights n}
    (optimum : NormalizedEdgeLP.minimize A c pairs.get (m : ℚ≥0) = some (q,w)) :
    runBest A c pairs T tape = NormalizedEdgeLPRound.runOptimal A c pairs (pick A w pairs) T tape := by
  simp only [runBest, NormalizedEdgeLPRound.runOptimal, optimum, Option.bind_some]

end DirectedFlowCutGap.NormalizedOptimalMode
