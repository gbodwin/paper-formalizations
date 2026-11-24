import DirectedFlowCutGap.ConcurrentEdgeMassBudget
import DirectedFlowCutGap.FractionalCoverGuesses
import DirectedFlowCutGap.RationalEdgeDecomposition

/-! Rational doubling grids supply a nearby feasible price and mass budget
without knowing the real comparator. -/
namespace DirectedFlowCutGap.ConcurrentEdgeBudgetGrid

open scoped BigOperators NNRat NNReal ENNReal
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeCappedPrices (floorPrice floor_le_objective capped_normalized)
open ConcurrentEdgeZeroPrices (positiveGraph)
open SparsestEdgeBridge (demandDistance)

variable {m n : ℕ}

def gridSteps (lo hi : ℚ≥0) : ℕ := (hi/lo).num.size

def grid (lo hi : ℚ≥0) : List ℚ≥0 :=
  (List.range (gridSteps lo hi + 2)).map fun k => lo * (2 : ℚ≥0)^k

theorem positive {lo hi b : ℚ≥0} (loPos : 0 < lo) (present : b ∈ grid lo hi) :
    0 < b := by
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp present
  positivity

theorem brackets (lo hi : ℚ≥0) (loPos : 0 < lo) (x : ℝ≥0)
    (low : (lo : ℝ≥0) ≤ x) (high : x ≤ (hi : ℝ≥0)) :
    ∃ b ∈ grid lo hi, x ≤ (b : ℝ≥0) ∧ (b : ℝ≥0) ≤ 2*x := by
  let q := hi/lo
  let L := gridSteps lo hi
  have ratio : q ≤ (q.num : ℚ≥0) := by
    calc
      q = (q.num : ℚ≥0)/(q.den : ℚ≥0) := (NNRat.num_div_den q).symm
      _ ≤ _ := div_le_self zero_le (by exact_mod_cast q.den_pos)
  have wide : (q.num : ℚ≥0) ≤ 2^L := by
    exact_mod_cast (Nat.lt_size_self q.num).le
  have hiSpan : hi ≤ lo*(2 : ℚ≥0)^L := by
    have span := (div_le_iff₀ loPos).mp (ratio.trans wide)
    exact span.trans_eq (mul_comm ..)
  have rx : (x : ℝ) ≤ ((lo : ℚ) : ℝ)*(2 : ℝ)^L := by
    have rational : (hi : ℚ) ≤ (lo : ℚ)*(2 : ℚ)^L := by
      exact_mod_cast hiSpan
    have real : ((hi : ℚ) : ℝ) ≤ ((lo : ℚ) : ℝ)*(2 : ℝ)^L := by
      exact_mod_cast rational
    exact (show (x : ℝ) ≤ ((hi : ℚ) : ℝ) from NNReal.coe_le_coe.mpr high).trans real
  have lx : ((lo : ℚ) : ℝ) ≤ (x : ℝ) := NNReal.coe_le_coe.mpr low
  obtain ⟨k,inside,left,right⟩ := FractionalCoverGuesses.doubling_bracket (lo : ℚ)
    (by exact_mod_cast loPos) (x : ℝ) L lx rx
  let b : ℚ≥0 := lo * (2 : ℚ≥0)^(k+1)
  have selected : b ∈ grid lo hi := by
    apply List.mem_map.mpr
    exact ⟨k+1, List.mem_range.mpr (by dsimp only [L] at inside; omega), rfl⟩
  have read : ((b : ℝ≥0) : ℝ) = 2 * (((lo : ℚ) : ℝ)*(2 : ℝ)^k) := by
    simp only [b, NNRat.cast_mul, NNRat.cast_pow, NNRat.cast_ofNat, NNReal.coe_mul, NNReal.coe_pow,
      NNReal.coe_ofNat, pow_succ]
    change ((lo : ℚ) : ℝ) * ((2 : ℝ)^k * 2) = _
    ac_rfl
  refine ⟨b,selected,NNReal.coe_le_coe.mp ?_,NNReal.coe_le_coe.mp ?_⟩
  · rwa [read]
  · change ((b : ℝ≥0) : ℝ) ≤ 2 * (x : ℝ)
    rw [read]
    exact mul_le_mul_of_nonneg_left left (by norm_num)

def costCeiling (A : Adjacency n) (c : Weights n) (m : ℕ) : ℚ≥0 :=
  (m : ℚ≥0) * RationalEdgeDecomposition.originalTotal A c

def massCeiling (n m : ℕ) : ℚ≥0 := (m : ℚ≥0)*(n : ℚ≥0)^2

def pairs (A : Adjacency n) (c : Weights n) (m : ℕ) : List (ℚ≥0 × ℚ≥0) :=
  (grid (floorPrice c) (costCeiling A c m)).flatMap fun B =>
    (grid 1 (massCeiling n m)).map fun U => (B,U)

theorem normalized_mass_lower (A : Adjacency n) (P : Vector (Edge n) m) (d : Fin m)
    (reach : ∀ i : Fin m, Nonempty (SimplePath (graph A) (P.get i).1 (P.get i).2))
    (w : Edge n → ℝ≥0) (normalized : (m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) w (P.get j)) :
    1 ≤ totalEdgeWeight (graph A) w := by
  let W := totalEdgeWeight (graph A) w
  have each (i : Fin m) : demandDistance (graph A) w (P.get i) ≤ W := by
    obtain ⟨p, label⟩ := edgeDistance_attained w (reach i)
    simp only [demandDistance, label, ENNReal.toNNReal_coe]
    exact Finset.sum_le_sum_of_subset p.edges_subset_graphEdges
  have scale := normalized.trans (Finset.sum_le_sum (fun i _ => each i))
  have result : (m : ℝ≥0) ≤ (m : ℝ≥0)*W := by simpa [nsmul_eq_mul] using scale
  have pos : (0 : ℝ≥0) < m := by exact_mod_cast (Nat.zero_le _).trans_lt d.isLt
  exact (le_of_mul_le_mul_left (by simpa only [mul_one] using result) pos)

theorem cap_bounds (A : Adjacency n) (c : Weights n) (m : ℕ) (w : Edge n → ℝ≥0) :
    weightedEdgeCost (graph A) (weights c) (fun e => min m (w e)) ≤ (costCeiling A c m : ℝ≥0) ∧
      totalEdgeWeight (graph A) (fun e => min m (w e)) ≤ (massCeiling n m : ℝ≥0) := by
  let E := graphEdges (graph A)
  have costs : (RationalEdgeDecomposition.originalTotal A c : ℝ≥0) =
      totalEdgeWeight (graph A) (weights c) := by
    simp only [RationalEdgeDecomposition.originalTotal, NNRat.cast_sum,
      RationalEdgeDecomposition.originalWeight_eq]
    exact_mod_cast WeakDecomposition.sum_actualEdgeWeight (graph A) (weights c)
  constructor
  · rw [costCeiling, NNRat.cast_mul, NNRat.cast_natCast, costs]
    change (∑ e ∈ E, weights c e * min (m : ℝ≥0) (w e)) ≤ (m : ℝ≥0) * ∑ e ∈ E, weights c e
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun e _ => (mul_le_mul_of_nonneg_left (min_le_left _ _) zero_le).trans_eq (mul_comm ..)
  · have card : (E.card : ℝ≥0) ≤ (n : ℝ≥0)^2 := by
      have le := Finset.card_le_univ E
      rw [Fintype.card_prod, Fintype.card_fin, ← pow_two] at le
      exact_mod_cast le
    rw [massCeiling, NNRat.cast_mul, NNRat.cast_natCast, NNRat.cast_pow]
    calc
      _ ≤ ∑ _e ∈ E, (m : ℝ≥0) := Finset.sum_le_sum fun e _ => min_le_left _ _
      _ = (m : ℝ≥0)*(E.card : ℝ≥0) := by simp [nsmul_eq_mul, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left card zero_le

theorem nearby_pair (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) (d : Fin m)
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (positivePaths : ∀ j : Fin m, Nonempty (SimplePath (graph (positiveGraph A c)) (P.get j).1 (P.get j).2))
    (w : Edge n → ℝ≥0) (normalized : (m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) w (P.get j)) :
    let u := fun e => min (m : ℝ≥0) (w e)
    ∃ B U : ℚ≥0, (B,U) ∈ pairs A c m ∧ 0 < B ∧ 0 < U ∧
      weightedEdgeCost (graph A) (weights c) u ≤ (B : ℝ≥0) ∧
      totalEdgeWeight (graph A) u ≤ (U : ℝ≥0) ∧
      (B : ℝ≥0) ≤ 2*weightedEdgeCost (graph A) (weights c) w ∧
      (U : ℝ≥0) ≤ 2*totalEdgeWeight (graph A) w := by
  let u (e : Edge n) := min (m : ℝ≥0) (w e)
  have normU := capped_normalized A P w reach normalized
  have bounds := cap_bounds A c m w
  have floor := ConcurrentEdgeCappedPrices.floor_positive c
  obtain ⟨B,pricePair,coverPrice,closePrice⟩ :=
    brackets (floorPrice c) (costCeiling A c m) floor _
      (floor_le_objective A c P d positivePaths u normU) bounds.1
  obtain ⟨U,massPair,coverMass,closeMass⟩ :=
    brackets 1 (massCeiling n m) zero_lt_one _ (by
      rw [NNRat.cast_one]
      exact normalized_mass_lower A P d reach u normU) bounds.2
  have price : weightedEdgeCost (graph A) (weights c) u ≤ weightedEdgeCost (graph A) (weights c) w :=
    Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (min_le_right _ _) zero_le
  have mass : totalEdgeWeight (graph A) u ≤ totalEdgeWeight (graph A) w :=
    Finset.sum_le_sum fun e _ => min_le_right _ _
  refine ⟨B,U,?_,positive floor pricePair,positive zero_lt_one massPair,coverPrice,coverMass,
    closePrice.trans (mul_le_mul_of_nonneg_left price zero_le),
    closeMass.trans (mul_le_mul_of_nonneg_left mass zero_le)⟩
  exact List.mem_flatMap.mpr ⟨B,pricePair,List.mem_map.mpr ⟨U,massPair,rfl⟩⟩

def candidates (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    List (Weights n) :=
  (pairs A c m).map fun (B,U) => ConcurrentEdgeMassBudget.solve hn A c P B U

theorem nearby_candidate (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2)
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (positivePaths : ∀ j : Fin m, Nonempty (SimplePath (graph (positiveGraph A c)) (P.get j).1 (P.get j).2))
    (w : Edge n → ℝ≥0) (normalized : (m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) w (P.get j)) :
    ∃ z ∈ candidates hn A c P,
      ((m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) (weights z) (P.get j)) ∧
      weightedEdgeCost (graph A) (weights c) (weights z) ≤ 12 * weightedEdgeCost (graph A) (weights c) w ∧
      totalEdgeWeight (graph A) (weights z) ≤ 12 * totalEdgeWeight (graph A) w := by
  obtain ⟨B,U,found,bp,up,pay,space,bigger,larger⟩ := nearby_pair A c P d reach positivePaths w normalized
  let z := ConcurrentEdgeMassBudget.solve hn A c P B U
  have spec := ConcurrentEdgeMassBudget.solve_bounds hn A c P B U bp up reach d different
    (fun e => min (m : ℝ≥0) (w e)) (capped_normalized A P w reach normalized) pay space
  refine ⟨z,List.mem_map.mpr ⟨(B,U),found,rfl⟩,spec.1,?_,?_⟩
  · exact spec.2.1.trans ((mul_le_mul_of_nonneg_left bigger zero_le).trans_eq (by ring))
  · exact spec.2.2.trans ((mul_le_mul_of_nonneg_left larger zero_le).trans_eq (by ring))

end DirectedFlowCutGap.ConcurrentEdgeBudgetGrid
