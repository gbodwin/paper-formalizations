import DirectedFlowCutGap.ConcurrentEdgeOracle
import DirectedFlowCutGap.SparsestNormalizedPotentials

/-! An iterative normalized edge cover uses joint shortest-path columns.
The initial version assumes positive prices on actual arcs. -/
namespace DirectedFlowCutGap.ConcurrentEdgeCover

open scoped BigOperators NNReal NNRat ENNReal
open BinaryFractionalWalkOracle (Adjacency graph decodeCost)
open RationalEdgeThresholds (Weights weights cost)
open ConcurrentEdgeOracle (Resource Edge Profile resource edge profileCoeff)
open FractionalCover (Row value objective value_ofFn)
open SparsestEdgeBridge (demandDistance)

variable {m n : ℕ}

theorem normalization_iff (A : Adjacency n) (P : Vector (Edge n) m)
    (w : Edge n → ℝ≥0)
    (reachable : ∀ d : Fin m, Nonempty (SimplePath (graph A) (P.get d).1 (P.get d).2))
    (target : ℝ≥0) :
    (target ≤ ∑ d : Fin m, demandDistance (graph A) w (P.get d)) ↔
      ∀ p : Profile A P, target ≤ ∑ d : Fin m, (p d).edgeWeight w := by
  constructor
  · intro normalized p
    refine normalized.trans (Finset.sum_le_sum fun d _ => ?_)
    unfold demandDistance
    have finite := fun h => ((edgeDistance_eq_top_iff (graph A) w (P.get d).1 (P.get d).2).mp h)
      (reachable d)
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal finite]
    exact edgeDistance_le_weight w (p d)
  · intro all
    have exactPath (d : Fin m) := edgeDistance_attained w (reachable d)
    choose path equation using exactPath
    have observed (d : Fin m) : demandDistance (graph A) w (P.get d) = (path d).edgeWeight w := by
      simp only [demandDistance, equation, ENNReal.toNNReal_coe]
    simpa only [observed] using all path

def priceRow (A : Adjacency n) (prices : Weights n) : Row (n*n) :=
  Vector.ofFn fun i =>
    let e := edge i
    if A[e.1.val][e.2.val] then FractionalCoverRawCore.rational (decodeCost (cost prices) e) else 1

private theorem price_of_arc (A : Adjacency n) (prices : Weights n) (e : Edge n)
    (arc : e ∈ graphEdges (graph A)) :
    (value (priceRow A prices) (resource e) : ℝ) = (weights prices e : ℝ) := by
  have isArc : A[e.1.val][e.2.val] = true := (mem_graphEdges _ _).mp arc
  simp only [priceRow, value_ofFn, ConcurrentEdgeOracle.edge_resource, isArc, ite_true]
  rfl

private theorem positive_prices (A : Adjacency n) (c : Weights n)
    (positive : ∀ e ∈ graphEdges (graph A), 0 < weights c e) :
    ∀ i, 0 < value (priceRow A c) i := by
  intro i
  by_cases h : A[(edge i).1.val][(edge i).2.val] = true
  · have present : edge i ∈ graphEdges (graph A) := (mem_graphEdges _ _).mpr h
    have price := price_of_arc A c (edge i) present
    rw [ConcurrentEdgeOracle.resource_edge] at price
    have value_pos : (0 : ℝ) < value (priceRow A c) i := price ▸ NNReal.coe_pos.mpr (positive _ present)
    exact_mod_cast value_pos
  · simp only [priceRow, value_ofFn, h]
    norm_num

def base (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) : Row (n*n) :=
  let cap := priceRow A c
  (MultiplicityCover.solve cap (ConcurrentEdgeOracle.oracle hn A P cap)).best

def solve (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) : Weights n :=
  let best := base hn A c P
  ConcurrentEdgeOracle.encoded (Vector.ofFn fun i => (m : ℚ) * value best i)

private theorem solve_read (hn : 0 < n) (A : Adjacency n) (c : Weights n)
    (P : Vector (Edge n) m) (nonneg : ∀ i, 0 ≤ value (base hn A c P) i) (e : Edge n) :
    (weights (solve hn A c P) e : ℝ) = (m : ℝ) * (value (base hn A c P) (resource e) : ℝ) := by
  let stored := Vector.ofFn fun i => (m : ℚ) * value (base hn A c P) i
  have nonnegative (i : Resource n) : 0 ≤ value stored i := by
    simp only [stored, value_ofFn]
    exact mul_nonneg (by positivity) (nonneg i)
  have exactValue := ConcurrentEdgeOracle.read_length stored nonnegative e
  have represented := congrArg (fun q : ℚ => (q : ℝ)) exactValue
  change (weights (solve hn A c P) e : ℝ) = _
  change ((FractionalCoverRawCore.rational (decodeCost (cost (ConcurrentEdgeOracle.encoded stored)) e)
    : ℚ) : ℝ) = _
  rw [represented]
  simp only [stored, value_ofFn, Rat.cast_mul, Rat.cast_natCast]

theorem solve_normalized (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (positive : ∀ e ∈ graphEdges (graph A), 0 < weights c e)
    (reachable : ∀ d : Fin m, Nonempty (SimplePath (graph A) (P.get d).1 (P.get d).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) :
    (m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) (weights (solve hn A c P)) (P.get j) := by
  let cap := priceRow A c
  let oracle := ConcurrentEdgeOracle.oracle hn A P cap
  have good := ConcurrentEdgeOracle.oracle_correct hn A P cap reachable d different
  have inv := MultiplicityCover.run_invariant cap (ConcurrentEdgeOracle.columns A P) oracle
    (Nat.mul_pos hn hn) (positive_prices A c positive) good (FractionalCover.fuel (n*n))
  have cover : MultiplicityCover.Feasible (ConcurrentEdgeOracle.columns A P) (base hn A c P) := inv.feasible
  apply (normalization_iff A P _ reachable _).mpr
  intro path
  let col : MultiplicityCover.Column (n*n) := Vector.ofFn (profileCoeff A P path)
  have valueCol (i : Resource n) : MultiplicityCover.coeff col i = profileCoeff A P path i :=
    Vector.getElem_ofFn i.isLt
  have member : col ∈ ConcurrentEdgeOracle.columns A P := ⟨path,valueCol⟩
  have required := cover.2 col member
  rw [ConcurrentEdgeOracle.profile_length A P col path valueCol] at required
  have realRequired : (1 : ℝ) ≤
      ∑ j : Fin m, ∑ e ∈ (path j).edges, (value (base hn A c P) (resource e) : ℝ) := by
    exact_mod_cast required
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_natCast, NNReal.coe_sum, SimplePath.edgeWeight, solve_read hn A c P cover.1,
    ← Finset.mul_sum]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left realRequired (by positivity : 0 ≤ (m : ℝ))

noncomputable def compare (A : Adjacency n) (m : ℕ) (w : Edge n → ℝ≥0) (i : Resource n) : ℝ :=
  if A[(edge i).1.val][(edge i).2.val] then (w (edge i) : ℝ) / m else 0

private theorem compare_arc (A : Adjacency n) (m : ℕ) (w : Edge n → ℝ≥0)
    (e : Edge n) (isArc : e ∈ graphEdges (graph A)) :
    compare A m w (resource e) = (w e : ℝ) / m := by
  have h : A[e.1.val][e.2.val] = true := (mem_graphEdges _ _).mp isArc
  simp only [compare, ConcurrentEdgeOracle.edge_resource, h, ite_true]

private theorem compare_feasible (A : Adjacency n) (P : Vector (Edge n) m) (w : Edge n → ℝ≥0)
    (mpos : (0 : ℝ) < m)
    (reachable : ∀ d : Fin m, Nonempty (SimplePath (graph A) (P.get d).1 (P.get d).2))
    (normalized : (m : ℝ≥0) ≤ ∑ d : Fin m, demandDistance (graph A) w (P.get d)) :
    MultiplicityCover.RealFeasible (ConcurrentEdgeOracle.columns A P) (compare A m w) := by
  constructor
  · intro i
    unfold compare
    split <;> positivity
  · intro col member
    obtain ⟨paths,entries⟩ := member
    rw [ConcurrentEdgeOracle.profile_eval A P col paths entries]
    have evaluated :
        (∑ d : Fin m, ∑ e ∈ (paths d).edges, compare A m w (resource e)) =
          ((∑ d : Fin m, (paths d).edgeWeight w : ℝ≥0) : ℝ)/(m : ℝ) := by
      simp only [NNReal.coe_sum, SimplePath.edgeWeight, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro e present
      exact compare_arc A m w e ((paths d).edges_subset_graphEdges present)
    rw [evaluated]
    have total := (normalization_iff A P w reachable _).mp normalized paths
    apply (le_div_iff₀ mpos).mpr
    simpa only [one_mul, NNReal.coe_natCast] using NNReal.coe_le_coe.mpr total

private theorem compare_price (A : Adjacency n) (c : Weights n) (m : ℕ) (w : Edge n → ℝ≥0) :
    (∑ i, (value (priceRow A c) i : ℝ) * compare A m w i) =
      (weightedEdgeCost (graph A) (weights c) w : ℝ)/(m : ℝ) := by
  rw [← (finProdFinEquiv : Edge n ≃ Resource n).sum_comp
    (fun i => (value (priceRow A c) i : ℝ) * compare A m w i)]
  change (∑ e : Edge n, (value (priceRow A c) (resource e) : ℝ) * compare A m w (resource e)) = _
  simp only [weightedEdgeCost, NNReal.coe_sum, Finset.sum_div, graphEdges, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases arc : (graph A).Adj e.1 e.2
  · have h : e ∈ graphEdges (graph A) := (mem_graphEdges _ _).mpr arc
    rw [price_of_arc A c e h, compare_arc A m w e h, ite_eq_left arc, NNReal.coe_mul, mul_div_assoc]
  · have absent : ¬A[e.1.val][e.2.val] = true := arc
    simp [compare, absent, arc]

theorem solve_price_le (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (positive : ∀ e ∈ graphEdges (graph A), 0 < weights c e)
    (reachable : ∀ d : Fin m, Nonempty (SimplePath (graph A) (P.get d).1 (P.get d).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2)
    (w : Edge n → ℝ≥0)
    (normalized : (m : ℝ≥0) ≤ ∑ d : Fin m, demandDistance (graph A) w (P.get d)) :
    (weightedEdgeCost (graph A) (weights c) (weights (solve hn A c P)) : ℝ) ≤
      3 * (weightedEdgeCost (graph A) (weights c) w : ℝ) := by
  let cap := priceRow A c
  let cost := fun e : Edge n => ((value cap (resource e) : ℝ) *
    (value (base hn A c P) (resource e) : ℝ))
  let cb : ℝ := weightedEdgeCost (graph A) (weights c) w
  let oracle := ConcurrentEdgeOracle.oracle hn A P cap
  have capPos := positive_prices A c positive
  have good := ConcurrentEdgeOracle.oracle_correct hn A P cap reachable d different
  have inv := MultiplicityCover.run_invariant cap (ConcurrentEdgeOracle.columns A P) oracle
    (Nat.mul_pos hn hn) capPos good (FractionalCover.fuel (n*n))
  have valid : MultiplicityCover.Feasible (ConcurrentEdgeOracle.columns A P) (base hn A c P) := inv.feasible
  have mpos : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_le _).trans_lt d.isLt
  have estimate := MultiplicityCover.solve_three_approximation_real cap (ConcurrentEdgeOracle.columns A P)
    oracle (Nat.mul_pos hn hn) capPos good _ (compare_feasible A P w mpos reachable normalized)
  have coverPrice : (objective cap (base hn A c P) : ℝ) ≤ 3 * (cb/(m : ℝ)) :=
    estimate.trans_eq (congrArg (fun q : ℝ => 3*q) (compare_price A c m w))
  have allPrice : (∑ e : Edge n, cost e) = (objective cap (base hn A c P) : ℝ) := by
    rw [objective, Rat.cast_sum]
    simp only [Rat.cast_mul, cost]
    exact (finProdFinEquiv : Edge n ≃ Resource n).sum_comp
      (fun i : Resource n => (value cap i : ℝ) * (value (base hn A c P) i : ℝ))
  have observed : (weightedEdgeCost (graph A) (weights c) (weights (solve hn A c P)) : ℝ) =
      (m : ℝ) * ∑ e ∈ graphEdges (graph A), cost e := by
    simp only [weightedEdgeCost, NNReal.coe_sum, NNReal.coe_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e inGraph
    rw [solve_read hn A c P valid.1, ← price_of_arc A c e inGraph]
    unfold cost cap
    ring
  rw [observed]
  calc
    _ ≤ (m : ℝ) * ∑ e : Edge n, cost e := by
      apply mul_le_mul_of_nonneg_left _ mpos.le
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro e _ _
      unfold cost
      have p : (0 : ℝ) ≤ value cap (resource e) := by exact_mod_cast (capPos (resource e)).le
      have v : (0 : ℝ) ≤ value (base hn A c P) (resource e) := by exact_mod_cast valid.1 (resource e)
      exact mul_nonneg p v
    _ ≤ (m : ℝ) * (3 * (cb/(m : ℝ))) := by rw [allPrice]; exact mul_le_mul_of_nonneg_left coverPrice mpos.le
    _ = 3 * cb := by field_simp [mpos.ne']

end DirectedFlowCutGap.ConcurrentEdgeCover
