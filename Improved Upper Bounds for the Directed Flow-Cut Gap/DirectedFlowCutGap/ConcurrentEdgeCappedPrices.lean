import DirectedFlowCutGap.ConcurrentEdgeZeroPrices

/-! Strictly positive prices for the joint-path covering iteration.
The perturbation uses an exact rational lower bound on every positive price. -/
namespace DirectedFlowCutGap.ConcurrentEdgeCappedPrices

open scoped BigOperators NNReal NNRat ENNReal
open BinaryFractionalWalkOracle (Adjacency graph decodeCost)
open RationalEdgeThresholds (Weights weights cost)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeZeroPrices (positiveGraph rawPrice rawPrice_eq)
open SparsestEdgeBridge (demandDistance)

variable {m n : ℕ}

def floorFactor (c : Weights n) (e : Edge n) : ℚ≥0 :=
  if 0 < rawPrice c e then min 1 (rawPrice c e) else 1

def floorPrice (c : Weights n) : ℚ≥0 := ∏ e : Edge n, floorFactor c e

theorem floor_positive (c : Weights n) : 0 < floorPrice c := by
  apply Finset.prod_pos
  intro e _
  unfold floorFactor
  split
  · exact lt_min zero_lt_one ‹0 < rawPrice c e›
  · exact zero_lt_one

theorem floor_le (c : Weights n) (e : Edge n) (positive : 0 < weights c e) :
    (floorPrice c : ℝ≥0) ≤ weights c e := by
  have raw : 0 < rawPrice c e := by
    rw [← rawPrice_eq] at positive
    exact_mod_cast positive
  have single := Finset.prod_le_prod_of_subset_of_le_one₀
    (f := floorFactor c) (Finset.subset_univ ({e} : Finset (Edge n))) (fun _ _ => zero_le)
    (by
      intro a _ _
      unfold floorFactor
      split
      · exact min_le_left _ _
      · exact le_rfl)
  rw [Finset.prod_singleton, floorFactor, ite_eq_left raw] at single
  rw [← rawPrice_eq]
  exact_mod_cast single.trans (min_le_right _ _)

def increment (n m : ℕ) (c : Weights n) : ℚ≥0 :=
  floorPrice c / ((m : ℚ≥0) * (n : ℚ≥0)^2)

def adjusted (m : ℕ) (c : Weights n) : Weights n :=
  Vector.ofFn fun u => Vector.ofFn fun v =>
    let p := rawPrice c (u,v)
    let q := if 0 < p then p else increment n m c
    (BinaryRawRational.encode (RawNonnegativeRational.Code.ofNNRat q)).1

theorem adjusted_eq (m : ℕ) (c : Weights n) (e : Edge n) :
    weights (adjusted m c) e =
      if 0 < weights c e then weights c e else (increment n m c : ℝ≥0) := by
  rcases e with ⟨u,v⟩
  have value : rawPrice (adjusted m c) (u,v) =
      if 0 < rawPrice c (u,v) then rawPrice c (u,v) else increment n m c := by
    simp only [rawPrice, cost, decodeCost, adjusted, Vector.getElem_ofFn, BinaryRawRational.encode_value,
      RawNonnegativeRational.Code.value_ofNNRat]
  rw [← rawPrice_eq, value]
  by_cases price : 0 < rawPrice c (u,v)
  · have real : 0 < weights c (u,v) := by
      rw [← rawPrice_eq]
      exact_mod_cast price
    rw [ite_eq_left price, ite_eq_left real, rawPrice_eq]
  · have real : ¬0 < weights c (u,v) := by
      rw [← rawPrice_eq]
      exact_mod_cast price
    rw [ite_eq_right price, ite_eq_right real]

theorem positive (c : Weights n) (hn : 0 < n) (hm : 0 < m) (e : Edge n) :
    0 < weights (adjusted m c) e := by
  have i : 0 < increment n m c := div_pos (floor_positive c) (by positivity)
  rw [adjusted_eq]
  split
  · assumption
  · exact_mod_cast i

theorem price_bounds (c : Weights n) (m : ℕ) (e : Edge n) :
    weights c e ≤ weights (adjusted m c) e ∧
      weights (adjusted m c) e ≤ weights c e + (increment n m c : ℝ≥0) := by
  rw [adjusted_eq]
  by_cases p : 0 < weights c e
  · rw [ite_eq_left p]
    exact ⟨le_rfl, le_add_of_nonneg_right zero_le⟩
  · have zero : weights c e = 0 := le_antisymm (le_of_not_gt p) zero_le
    simp [zero]

private theorem cap_path {A : Adjacency n} {s t : Fin n} (p : SimplePath (graph A) s t)
    (w : Edge n → ℝ≥0) (C : ℝ≥0) :
    min C (p.edgeWeight w) ≤ p.edgeWeight (fun e => min C (w e)) := by
  classical
  by_cases cap : ∃ e ∈ p.edges, C ≤ w e
  · obtain ⟨e, present, high⟩ := cap
    exact (min_le_left _ _).trans ((min_eq_left high).symm.trans_le
      (Finset.single_le_sum (f := fun e => min C (w e)) (fun _ _ => zero_le) present))
  · have eq : p.edgeWeight (fun e => min C (w e)) = p.edgeWeight w := by
      apply Finset.sum_congr rfl
      intro e present
      exact min_eq_right (le_of_lt (lt_of_not_ge (fun high => cap ⟨e,present,high⟩)))
    exact (min_le_right _ _).trans_eq eq.symm

theorem capped_normalized (A : Adjacency n) (P : Vector (Edge n) m) (w : Edge n → ℝ≥0)
    (reachable : ∀ d : Fin m, Nonempty (SimplePath (graph A) (P.get d).1 (P.get d).2))
    (normalized : (m : ℝ≥0) ≤ ∑ d : Fin m, demandDistance (graph A) w (P.get d)) :
    (m : ℝ≥0) ≤ ∑ d : Fin m, demandDistance (graph A) (fun e => min m (w e)) (P.get d) := by
  let u : Edge n → ℝ≥0 := fun e => min m (w e)
  let x (i : Fin m) := demandDistance (graph A) w (P.get i)
  let y (i : Fin m) := demandDistance (graph A) u (P.get i)
  have lower (i : Fin m) : min (m : ℝ≥0) (x i) ≤ y i := by
    let p := P.get i
    have old : edgeDistance (graph A) w p.1 p.2 ≠ ⊤ :=
      fun absent => ((edgeDistance_eq_top_iff (graph A) w p.1 p.2).mp absent) (reachable i)
    have new : edgeDistance (graph A) u p.1 p.2 ≠ ⊤ :=
      fun absent => ((edgeDistance_eq_top_iff (graph A) u p.1 p.2).mp absent) (reachable i)
    apply ENNReal.coe_le_coe.mp
    change ((min (m : ℝ≥0) (x i) : ℝ≥0) : ℝ≥0∞) ≤
      ((edgeDistance (graph A) u p.1 p.2).toNNReal : ℝ≥0∞)
    rw [ENNReal.coe_toNNReal new]
    apply (coe_le_edgeDistance_iff (graph A) u p.1 p.2 _).mpr
    intro path
    have distance : x i ≤ path.edgeWeight w := by
      apply ENNReal.coe_le_coe.mp
      change ((edgeDistance (graph A) w p.1 p.2).toNNReal : ℝ≥0∞) ≤ _
      rw [ENNReal.coe_toNNReal old]
      exact edgeDistance_le_weight w path
    exact (min_le_min le_rfl distance).trans (cap_path path w m)
  have total : (m : ℝ≥0) ≤ ∑ i, min (m : ℝ≥0) (x i) := by
    by_cases reached : ∃ i, (m : ℝ≥0) ≤ x i
    · obtain ⟨i, bound⟩ := reached
      simpa only [min_eq_left bound] using Finset.single_le_sum
        (f := fun j => min (m : ℝ≥0) (x j)) (fun _ _ => zero_le) (Finset.mem_univ i)
    · refine normalized.trans_eq ?_
      exact Finset.sum_congr rfl fun i _ => (min_eq_right
        (le_of_lt (lt_of_not_ge (fun bound => reached ⟨i,bound⟩)))).symm
  exact total.trans (Finset.sum_le_sum (fun i _ => lower i))

theorem floor_le_objective (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (nonempty : Fin m)
    (positivePaths : ∀ i : Fin m, Nonempty (SimplePath (graph (positiveGraph A c)) (P.get i).1 (P.get i).2))
    (w : Edge n → ℝ≥0)
    (normalized : (m : ℝ≥0) ≤ ∑ d : Fin m, demandDistance (graph A) w (P.get d)) :
    (floorPrice c : ℝ≥0) ≤ weightedEdgeCost (graph A) (weights c) w := by
  let distance (d : Fin m) := demandDistance (graph A) w (P.get d)
  have exceeds : ∃ d, 1 ≤ distance d := by
    by_contra! low
    have smaller := Finset.sum_lt_sum_of_nonempty
      (⟨nonempty,Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin m)).Nonempty) (fun d _ => low d)
    have total : (∑ _ : Fin m, (1 : ℝ≥0)) = (m : ℝ≥0) := by simp [nsmul_eq_mul]
    exact (not_le_of_gt (smaller.trans_eq total)) normalized
  obtain ⟨i, far⟩ := exceeds
  obtain ⟨p⟩ := positivePaths i
  let q : SimplePath (graph A) (P.get i).1 (P.get i).2 :=
    { p with adjacent := fun j => ((ConcurrentEdgeZeroPrices.adj_iff A c _ _).mp (p.adjacent j)).1 }
  have distance_le : distance i ≤ q.edgeWeight w := by
    have finite : edgeDistance (graph A) w (P.get i).1 (P.get i).2 ≠ ⊤ :=
      fun empty => ((edgeDistance_eq_top_iff (graph A) w (P.get i).1 (P.get i).2).mp empty) ⟨q⟩
    apply ENNReal.coe_le_coe.mp
    change ((edgeDistance (graph A) w (P.get i).1 (P.get i).2).toNNReal : ℝ≥0∞) ≤ _
    rw [ENNReal.coe_toNNReal finite]
    exact edgeDistance_le_weight w q
  let floor : ℝ≥0 := floorPrice c
  calc
    floor = floor*1 := (mul_one _).symm
    _ ≤ floor * q.edgeWeight w := mul_le_mul_of_nonneg_left (far.trans distance_le) zero_le
    _ = ∑ e ∈ q.edges, floor*w e := by rw [SimplePath.edgeWeight, Finset.mul_sum]
    _ ≤ ∑ e ∈ q.edges, weights c e*w e := by
      apply Finset.sum_le_sum
      intro e belongs
      have pEdge : e ∈ p.edges := belongs
      have costPositive := ((ConcurrentEdgeZeroPrices.adj_iff A c e.1 e.2).mp (p.edge_adj pEdge)).2
      exact mul_le_mul_of_nonneg_right (floor_le c e costPositive) zero_le
    _ ≤ weightedEdgeCost (graph A) (weights c) w :=
      Finset.sum_le_sum_of_subset q.edges_subset_graphEdges

theorem adjusted_price_le (A : Adjacency n) (c : Weights n) (m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (w : Edge n → ℝ≥0) :
    weightedEdgeCost (graph A) (weights (adjusted m c)) (fun e => min m (w e)) ≤
      weightedEdgeCost (graph A) (weights c) w + (floorPrice c : ℝ≥0) := by
  let q (e : Edge n) := min (m : ℝ≥0) (w e)
  let step : ℝ≥0 := increment n m c
  let E := graphEdges (graph A)
  have cardBound : (E.card : ℝ≥0) ≤ ((n*n : ℕ) : ℝ≥0) := by
    have raw := Finset.card_le_univ E
    rw [Fintype.card_prod, Fintype.card_fin] at raw
    exact_mod_cast raw
  have entry (e : Edge n) :
      weights (adjusted m c) e * q e ≤ weights c e * w e + step*(m : ℝ≥0) := by
    calc
      _ ≤ (weights c e + step) * q e := mul_le_mul_of_nonneg_right (price_bounds c m e).2 zero_le
      _ = weights c e * q e + step * q e := add_mul ..
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (min_le_right _ _) zero_le)
        (mul_le_mul_of_nonneg_left (min_le_left _ _) zero_le)
  have extra : (∑ _e ∈ E, step*(m : ℝ≥0)) ≤ (floorPrice c : ℝ≥0) := by
    calc
      _ = (E.card : ℝ≥0) * (step*(m : ℝ≥0)) := by simp [nsmul_eq_mul]
      _ ≤ ((n*n : ℕ) : ℝ≥0) * (step*(m : ℝ≥0)) :=
        mul_le_mul_of_nonneg_right cardBound zero_le
      _ = _ := by
        simp only [step, increment, NNRat.cast_div, NNRat.cast_mul, NNRat.cast_natCast,
          NNRat.cast_pow, Nat.cast_mul]
        have hnNe : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
        have hmNe : (m : ℝ≥0) ≠ 0 := by exact_mod_cast hm.ne'
        field_simp [hnNe, hmNe]
  unfold weightedEdgeCost
  refine (Finset.sum_le_sum fun e _ => entry e).trans ?_
  rw [Finset.sum_add_distrib]
  exact add_le_add le_rfl extra

def solve (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) : Weights n :=
  match ConcurrentEdgeZeroPrices.detect A c P with
  | some _ => ConcurrentEdgeZeroPrices.freeLength c m
  | none => ConcurrentEdgeCover.solve hn A (adjusted m c) P

theorem solve_spec (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (reachable : ∀ d : Fin m, Nonempty (SimplePath (graph A) (P.get d).1 (P.get d).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2)
    (w : Edge n → ℝ≥0)
    (normalized : (m : ℝ≥0) ≤ ∑ d : Fin m, demandDistance (graph A) w (P.get d)) :
    ((m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) (weights (solve hn A c P)) (P.get j)) ∧
      (weightedEdgeCost (graph A) (weights c) (weights (solve hn A c P)) : ℝ) ≤
        6 * (weightedEdgeCost (graph A) (weights c) w : ℝ) := by
  have hm : 0 < m := (Nat.zero_le _).trans_lt d.isLt
  cases found : ConcurrentEdgeZeroPrices.detect A c P with
  | some j =>
    rw [solve, found]
    refine ⟨ConcurrentEdgeZeroPrices.free_normalized A c P j (reachable j)
      (ConcurrentEdgeZeroPrices.detected found), ?_⟩
    rw [ConcurrentEdgeZeroPrices.free_objective, NNReal.coe_zero]
    positivity
  | none =>
    have pos : ∀ e ∈ graphEdges (graph A), 0 < weights (adjusted m c) e :=
      fun e _ => positive c hn hm e
    rw [solve, found]
    refine ⟨ConcurrentEdgeCover.solve_normalized hn A (adjusted m c) P pos reachable d different, ?_⟩
    have bound := ConcurrentEdgeCover.solve_price_le hn A (adjusted m c) P pos reachable d different
      (fun e => min m (w e)) (capped_normalized A P w reachable normalized)
    have floor := floor_le_objective A c P d (ConcurrentEdgeZeroPrices.all_reachable found) w normalized
    have comp := (adjusted_price_le A c m hn hm w).trans (add_le_add le_rfl floor)
    have real := NNReal.coe_le_coe.mpr comp
    rw [NNReal.coe_add] at real
    have price :
        weightedEdgeCost (graph A) (weights c) (weights (ConcurrentEdgeCover.solve hn A (adjusted m c) P)) ≤
          weightedEdgeCost (graph A) (weights (adjusted m c))
            (weights (ConcurrentEdgeCover.solve hn A (adjusted m c) P)) := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_right (price_bounds c m e).1 zero_le
    linarith [NNReal.coe_le_coe.mpr price]

end DirectedFlowCutGap.ConcurrentEdgeCappedPrices
