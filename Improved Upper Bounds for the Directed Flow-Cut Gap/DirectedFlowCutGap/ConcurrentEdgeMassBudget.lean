import DirectedFlowCutGap.ConcurrentEdgeCappedPrices

/-! Joint bounded optimization of original price and normalized mass.
Each original arc gets its scaled price plus a uniform mass charge. -/
namespace DirectedFlowCutGap.ConcurrentEdgeMassBudget

open scoped BigOperators NNReal NNRat
open BinaryFractionalWalkOracle (Adjacency graph decodeCost)
open RationalEdgeThresholds (Weights weights cost)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeZeroPrices (rawPrice rawPrice_eq)
open SparsestEdgeBridge (demandDistance)

variable {m n : ℕ}

def reprice (c : Weights n) (B U : ℚ≥0) : Weights n :=
  Vector.ofFn fun u => Vector.ofFn fun v =>
    let q := rawPrice c (u,v)/B + 1/U
    (BinaryRawRational.encode (RawNonnegativeRational.Code.ofNNRat q)).1

theorem reprice_eq (c : Weights n) (B U : ℚ≥0) (e : Edge n) :
    weights (reprice c B U) e = weights c e/(B : ℝ≥0) + 1/(U : ℝ≥0) := by
  rcases e with ⟨u,v⟩
  have value : rawPrice (reprice c B U) (u,v) = rawPrice c (u,v)/B + 1/U := by
    simp only [rawPrice, cost, decodeCost, reprice, Vector.getElem_ofFn,
      BinaryRawRational.encode_value, RawNonnegativeRational.Code.value_ofNNRat]
  rw [← rawPrice_eq, value]
  simp only [NNRat.cast_add, NNRat.cast_div, NNRat.cast_one, rawPrice_eq]

theorem reprice_cost (A : Adjacency n) (c : Weights n) (B U : ℚ≥0) (w : Edge n → ℝ≥0) :
    weightedEdgeCost (graph A) (weights (reprice c B U)) w =
      weightedEdgeCost (graph A) (weights c) w/(B : ℝ≥0) + totalEdgeWeight (graph A) w/(U : ℝ≥0) := by
  unfold weightedEdgeCost totalEdgeWeight
  simp only [Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [reprice_eq]
  simp only [div_eq_mul_inv]
  ring

def solve (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (B U : ℚ≥0) : Weights n :=
  ConcurrentEdgeCover.solve hn A (reprice c B U) P

theorem solve_bounds (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (B U : ℚ≥0) (Bpos : 0 < B) (Upos : 0 < U)
    (reachable : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2)
    (w : Edge n → ℝ≥0)
    (normalized : (m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) w (P.get j))
    (price : weightedEdgeCost (graph A) (weights c) w ≤ (B : ℝ≥0))
    (mass : totalEdgeWeight (graph A) w ≤ (U : ℝ≥0)) :
    let z := weights (solve hn A c P B U)
    ((m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) z (P.get j)) ∧
      weightedEdgeCost (graph A) (weights c) z ≤ 6*(B : ℝ≥0) ∧
      totalEdgeWeight (graph A) z ≤ 6*(U : ℝ≥0) := by
  let c' := reprice c B U
  let z := weights (solve hn A c P B U)
  have bp : (0 : ℝ≥0) < B := by exact_mod_cast Bpos
  have up : (0 : ℝ≥0) < U := by exact_mod_cast Upos
  have positive : ∀ e ∈ graphEdges (graph A), 0 < weights c' e := by
    intro e _
    change 0 < weights (reprice c B U) e
    rw [reprice_eq]
    exact add_pos_of_nonneg_of_pos zero_le (div_pos zero_lt_one up)
  have normalizedZ := ConcurrentEdgeCover.solve_normalized hn A c' P positive reachable d different
  have mixed : weightedEdgeCost (graph A) (weights c') w ≤ 2 := by
    change weightedEdgeCost (graph A) (weights (reprice c B U)) w ≤ 2
    rw [reprice_cost]
    have p := (div_le_one₀ bp).mpr price
    have u := (div_le_one₀ up).mpr mass
    exact (add_le_add p u).trans_eq (by norm_num)
  have paid := ConcurrentEdgeCover.solve_price_le hn A c' P positive reachable d different w normalized
  have bound : weightedEdgeCost (graph A) (weights c') z ≤ 6 := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_ofNat]
    exact paid.trans ((mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr mixed) (by norm_num)).trans_eq
      (by norm_num))
  have sum : weightedEdgeCost (graph A) (weights c) z/(B : ℝ≥0) +
      totalEdgeWeight (graph A) z/(U : ℝ≥0) ≤ 6 := (reprice_cost A c B U z) ▸ bound
  refine ⟨normalizedZ, (div_le_iff₀ bp).mp ?_, (div_le_iff₀ up).mp ?_⟩
  · exact (le_add_of_nonneg_right zero_le).trans sum
  · exact (le_add_of_nonneg_left zero_le).trans sum

end DirectedFlowCutGap.ConcurrentEdgeMassBudget
