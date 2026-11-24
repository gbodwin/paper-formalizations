import DirectedFlowCutGap.ConcurrentVertexBudget

/-! A generated vertex assignment bounds cost and mass against the same
real comparator. The algorithm does not receive that comparator. -/
namespace DirectedFlowCutGap.ConcurrentVertexBudgetGrid

open scoped BigOperators NNReal NNRat
open BinaryFractionalWalkOracle (Adjacency graph)
open BinaryFractionalRows (Row)
open ConcurrentEdgeOracle (Edge)
open RationalSparsestVertexDistances (weights)
open SparsestVertexBridge (demandDistance)
open ConcurrentVertexBudget (raw raw_eq pairs candidate candidate_bounds freeDemand floorPrice cap_normalized)
open ConcurrentEdgeBudgetGrid (grid brackets)

variable {m n : ℕ}

private theorem cap_bounds (c : Row n) (m : ℕ) (w : Fin n → ℝ≥0) :
    weightedCost (weights c) (fun v => min m (w v)) ≤ (ConcurrentVertexBudget.priceCeiling c m : ℝ≥0) ∧
      totalWeight (fun v => min m (w v)) ≤ (ConcurrentVertexBudget.massCeiling n m : ℝ≥0) := by
  constructor
  · unfold weightedCost ConcurrentVertexBudget.priceCeiling
    simp only [NNRat.cast_mul,NNRat.cast_natCast,NNRat.cast_sum,raw_eq,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    exact (mul_le_mul_of_nonneg_left (min_le_left ..) zero_le).trans_eq (mul_comm ..)
  · unfold totalWeight ConcurrentVertexBudget.massCeiling
    simp only [NNRat.cast_mul,NNRat.cast_natCast]
    calc
      _ ≤ ∑ _v : Fin n, (m : ℝ≥0) := Finset.sum_le_sum (fun v _ => min_le_left ..)
      _ = _ := by simp [nsmul_eq_mul,mul_comm]

theorem pair_positive (c : Row n) (m : ℕ) {B U : ℚ≥0} (member : (B,U) ∈ pairs c m) :
    0 < B ∧ 0 < U := by
  obtain ⟨b,price,other⟩ := List.mem_flatMap.mp member
  obtain ⟨u,mass,equal⟩ := List.mem_map.mp other
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
  exact ⟨ConcurrentEdgeBudgetGrid.positive (ConcurrentVertexBudget.floor_positive c) price,
    ConcurrentEdgeBudgetGrid.positive zero_lt_one mass⟩

def candidates (hn : 0 < n) (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m) : List (Row n) :=
  (pairs c m).map fun (B,U) => candidate hn A c P B U

theorem normalized (hn : 0 < n) (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    (reach : ∀ i : Fin m, Nonempty (SimplePath (graph A) (P.get i).1 (P.get i).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) (noArc : ¬ (graph A).Adj (P.get d).1 (P.get d).2)
    {z : Row n} (found : z ∈ candidates hn A c P) :
    (m : ℝ≥0) ≤ ∑ i, demandDistance (graph A) (weights z) (P.get i) := by
  obtain ⟨⟨B,U⟩,member,rfl⟩ := List.mem_map.mp found
  have normal := VertexNormalizedPotentials.normalized_of_nonadjacent (graph A) P.get
    (m : ℝ≥0) d (reach d) different noArc
  have Up : (0 : ℝ≥0) < U := by exact_mod_cast (pair_positive c m member).2
  have price (v : Fin n) : 0 < weights (ConcurrentVertexBudget.reprice c B U) v := by
    rw [ConcurrentVertexBudget.reprice_eq]
    exact add_pos_of_nonneg_of_pos zero_le (div_pos zero_lt_one Up)
  exact (ConcurrentVertexCover.solve_spec hn A _ P price reach d different noArc (fun _ => m) normal).1

theorem nearby (hn : 0 < n) (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    (reach : ∀ i : Fin m, Nonempty (SimplePath (graph A) (P.get i).1 (P.get i).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) (noArc : ¬ (graph A).Adj (P.get d).1 (P.get d).2)
    (noFree : freeDemand A c P = none)
    (w : Fin n → ℝ≥0) (normal : (m : ℝ≥0) ≤ ∑ i, demandDistance (graph A) w (P.get i)) :
    ∃ z ∈ candidates hn A c P,
      weightedCost (weights c) (weights z) ≤ 12*weightedCost (weights c) w ∧
      totalWeight (weights z) ≤ 12*totalWeight w := by
  let u (v : Fin n) := min (m : ℝ≥0) (w v)
  have valid := cap_normalized A P w reach normal
  have limits := cap_bounds c m w
  obtain ⟨B,fee,paid,closeB⟩ := brackets (floorPrice c) (ConcurrentVertexBudget.priceCeiling c m)
    (ConcurrentVertexBudget.floor_positive c) (weightedCost (weights c) u)
    (ConcurrentVertexBudget.floor_le_cost A c P d noFree u valid) limits.1
  obtain ⟨U,mass,light,closeU⟩ := brackets 1 (ConcurrentVertexBudget.massCeiling n m)
    zero_lt_one (totalWeight u) (by rw [NNRat.cast_one]; exact ConcurrentVertexBudget.mass_lower A P d reach u valid)
    limits.2
  have member : (B,U) ∈ pairs c m :=
    List.mem_flatMap.mpr ⟨B,fee,List.mem_map.mpr ⟨U,mass,rfl⟩⟩
  obtain ⟨Bp,Up⟩ := pair_positive c m member
  obtain ⟨_,costU,massU⟩ := candidate_bounds hn A c P B U Bp Up reach d different noArc u valid paid light
  have price : weightedCost (weights c) u ≤ weightedCost (weights c) w := by
    exact Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (min_le_right ..) zero_le)
  have size : totalWeight u ≤ totalWeight w := Finset.sum_le_sum (fun v _ => min_le_right ..)
  refine ⟨candidate hn A c P B U,List.mem_map.mpr ⟨(B,U),member,rfl⟩,?_ ,?_⟩
  · have b := closeB.trans (mul_le_mul_of_nonneg_left price zero_le)
    exact costU.trans ((mul_le_mul_of_nonneg_left b (by positivity)).trans_eq (by ring))
  · have u := closeU.trans (mul_le_mul_of_nonneg_left size zero_le)
    exact massU.trans ((mul_le_mul_of_nonneg_left u (by positivity)).trans_eq (by ring))

end DirectedFlowCutGap.ConcurrentVertexBudgetGrid
