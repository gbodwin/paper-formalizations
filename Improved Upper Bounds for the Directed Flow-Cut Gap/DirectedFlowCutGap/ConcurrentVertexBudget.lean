import DirectedFlowCutGap.ConcurrentVertexCover
import DirectedFlowCutGap.ConcurrentEdgeBudgetGrid
import DirectedFlowCutGap.RationalVertexSparsityCode

/-! Generate original price and total-mass budgets for the bounded vertex
cover. A mask of free vertices certifies the zero-price alternative. -/
namespace DirectedFlowCutGap.ConcurrentVertexBudget

open scoped BigOperators NNReal NNRat ENNReal
open BinaryFractionalWalkOracle (Adjacency graph)
open BinaryFractionalRows (Row)
open ConcurrentEdgeOracle (Edge Profile)
open RationalSparsestVertexDistances (weights)
open SparsestVertexBridge (demandDistance)
open EncodedUnitCostReplication (selectedSet)
open RetainedGridState (Flags)
open ConcurrentEdgeBudgetGrid (grid brackets positive)
open RawNonnegativeRational (Code)

variable {m n : ℕ}

def raw (c : Row n) (v : Fin n) : ℚ≥0 := (BinaryRational.decode (c.get v)).value
theorem raw_eq (c : Row n) (v : Fin n) : (raw c v : ℝ≥0) = weights c v := rfl

def freeMask (c : Row n) : Flags n :=
  Vector.ofFn fun v => decide (raw c v = 0)

theorem free_mem (c : Row n) (v : Fin n) : v ∈ selectedSet (freeMask c) ↔ weights c v = 0 := by
  have cast : ((raw c v : ℝ≥0) = 0) ↔ raw c v = 0 := by
    rw [← NNRat.cast_zero (α := ℝ≥0)]
    exact NNRat.cast_injective.eq_iff
  rw [← raw_eq,cast]
  simp [selectedSet,freeMask]

def freeDemand (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m) : Option (Fin m) :=
  (List.finRange m).find? fun i => RationalVertexSparsityCode.separates A (freeMask c) (P.get i)

theorem free_found (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m) {i : Fin m}
    (found : freeDemand A c P = some i) :
    CutsPair (graph A) (selectedSet (freeMask c)) (P.get i).1 (P.get i).2 := by
  apply (RationalVertexSparsityCode.separates_eq A (freeMask c) (P.get i)).mp
  exact List.find?_some (p := fun j : Fin m => RationalVertexSparsityCode.separates A (freeMask c) (P.get j)) found

theorem free_zero (c : Row n) : cutCost (weights c) (selectedSet (freeMask c)) = 0 := by
  exact Finset.sum_eq_zero fun v inside => (free_mem c v).mp inside

theorem positive_paths (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    (none : freeDemand A c P = none) :
    ∀ i : Fin m, ∃ path : SimplePath (graph A) (P.get i).1 (P.get i).2,
      ∀ v ∈ path.internalVertices, 0 < weights c v := by
  intro i
  have miss := (List.find?_eq_none.mp none) i (List.mem_finRange i)
  have no : ¬ CutsPair (graph A) (selectedSet (freeMask c)) (P.get i).1 (P.get i).2 :=
    fun cut => miss ((RationalVertexSparsityCode.separates_eq A (freeMask c) (P.get i)).mpr cut)
  obtain ⟨p,avoid⟩ := (not_cutsPair_iff ..).mp no
  exact ⟨p,fun v present => zero_lt_iff.mpr (fun zero => avoid v present ((free_mem c v).mpr zero))⟩

def floorFactor (c : Row n) (v : Fin n) : ℚ≥0 :=
  if 0 < raw c v then min 1 (raw c v) else 1

def floorPrice (c : Row n) : ℚ≥0 := ∏ v, floorFactor c v

theorem floor_positive (c : Row n) : 0 < floorPrice c := by
  apply Finset.prod_pos
  intro v _
  unfold floorFactor
  split
  · exact lt_min zero_lt_one ‹0 < raw c v›
  · exact zero_lt_one

theorem floor_le (c : Row n) (v : Fin n) (positive : 0 < weights c v) :
    (floorPrice c : ℝ≥0) ≤ weights c v := by
  have small : floorPrice c ≤ floorFactor c v := by
    have h := Finset.prod_le_prod_of_subset_of_le_one₀ (f := floorFactor c)
      (Finset.subset_univ ({v} : Finset (Fin n))) (fun _ _ => zero_le)
      (fun x _ _ => by unfold floorFactor; split; exact min_le_left ..; exact le_rfl)
    simpa only [floorPrice,Finset.prod_singleton] using h
  have rawPos : 0 < raw c v := by rw [← raw_eq] at positive; exact_mod_cast positive
  rw [floorFactor,ite_eq_left rawPos] at small
  have h := small.trans (min_le_right 1 (raw c v))
  rw [← raw_eq]
  exact_mod_cast h

theorem floor_le_cost (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m) (d : Fin m)
    (none : freeDemand A c P = none) (w : Fin n → ℝ≥0)
    (normal : (m : ℝ≥0) ≤ ∑ i, demandDistance (graph A) w (P.get i)) :
    (floorPrice c : ℝ≥0) ≤ weightedCost (weights c) w := by
  let F := (floorPrice c : ℝ≥0)
  let C := weightedCost (weights c) w
  have each (i : Fin m) : F*demandDistance (graph A) w (P.get i) ≤ C := by
    obtain ⟨p,pos⟩ := positive_paths A c P none i
    have finite : vertexDistance (graph A) w (P.get i).1 (P.get i).2 ≠ ⊤ :=
      fun top => ((vertexDistance_eq_top_iff (graph A) w _ _).mp top) ⟨p⟩
    have dist : demandDistance (graph A) w (P.get i) ≤ p.weight w := by
      apply ENNReal.coe_le_coe.mp
      rw [demandDistance,ENNReal.coe_toNNReal finite]
      exact vertexDistance_le_weight w p
    refine (mul_le_mul_of_nonneg_left dist zero_le).trans ?_
    simp only [SimplePath.weight,Finset.mul_sum,C,weightedCost]
    exact (Finset.sum_le_sum (fun v present => mul_le_mul_of_nonneg_right (floor_le c v (pos v present)) zero_le)).trans
      (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
  have large : F*(m : ℝ≥0) ≤ C*(m : ℝ≥0) := calc
    _ ≤ F*(∑ i, demandDistance (graph A) w (P.get i)) := mul_le_mul_of_nonneg_left normal zero_le
    _ ≤ ∑ _i : Fin m, C := by rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun i _ => each i)
    _ = _ := by simp [nsmul_eq_mul,mul_comm]
  have mpos : (0 : ℝ≥0) < m := by exact_mod_cast (Nat.zero_le _).trans_lt d.isLt
  exact le_of_mul_le_mul_right large mpos

private theorem cap_path {G : Digraph (Fin n)} {s t : Fin n} (p : SimplePath G s t)
    (w : Fin n → ℝ≥0) (target : ℝ≥0) :
    min target (p.weight w) ≤ p.weight (fun v => min target (w v)) := by
  classical
  by_cases wide : ∃ v ∈ p.internalVertices, target ≤ w v
  · obtain ⟨v,inside,large⟩ := wide
    exact (min_le_left ..).trans ((min_eq_left large).symm.trans_le
      (Finset.single_le_sum (f := fun u => min target (w u)) (fun _ _ => zero_le) inside))
  · have eq : p.weight (fun v => min target (w v)) = p.weight w := by
      apply Finset.sum_congr rfl
      intro v inside
      exact min_eq_right (le_of_not_ge (fun big => wide ⟨v,inside,big⟩))
    exact (min_le_right ..).trans_eq eq.symm

theorem cap_normalized (A : Adjacency n) (P : Vector (Edge n) m) (w : Fin n → ℝ≥0)
    (reach : ∀ i : Fin m, Nonempty (SimplePath (graph A) (P.get i).1 (P.get i).2))
    (normal : (m : ℝ≥0) ≤ ∑ i, demandDistance (graph A) w (P.get i)) :
    (m : ℝ≥0) ≤ ∑ i, demandDistance (graph A) (fun v => min m (w v)) (P.get i) := by
  apply (ConcurrentVertexCover.normalization_iff A P _ reach _).mpr
  intro paths
  have old := (ConcurrentVertexCover.normalization_iff A P w reach _).mp normal paths
  have minimum : (m : ℝ≥0) ≤ ∑ i, min (m : ℝ≥0) ((paths i).weight w) := by
    by_cases high : ∃ i : Fin m, (m : ℝ≥0) ≤ (paths i).weight w
    · obtain ⟨i,large⟩ := high
      simpa only [min_eq_left large] using Finset.single_le_sum
        (f := fun j => min (m : ℝ≥0) ((paths j).weight w)) (fun _ _ => zero_le) (Finset.mem_univ i)
    · exact old.trans_eq (Finset.sum_congr rfl fun i _ =>
        (min_eq_right (le_of_not_ge (fun large => high ⟨i,large⟩))).symm)
  exact minimum.trans (Finset.sum_le_sum (fun i _ => cap_path (paths i) w m))

theorem mass_lower (A : Adjacency n) (P : Vector (Edge n) m) (d : Fin m)
    (reach : ∀ i : Fin m, Nonempty (SimplePath (graph A) (P.get i).1 (P.get i).2))
    (w : Fin n → ℝ≥0) (normal : (m : ℝ≥0) ≤ ∑ i, demandDistance (graph A) w (P.get i)) :
    1 ≤ totalWeight w := by
  have each (i : Fin m) : demandDistance (graph A) w (P.get i) ≤ totalWeight w := by
    obtain ⟨p,equal⟩ := vertexDistance_attained w (reach i)
    simp only [demandDistance,equal,ENNReal.toNNReal_coe]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have sum := normal.trans (Finset.sum_le_sum (fun i _ => each i))
  have actual : (m : ℝ≥0)*1 ≤ (m : ℝ≥0)*totalWeight w := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using sum
  have mpos : (0 : ℝ≥0) < m := by exact_mod_cast (Nat.zero_le _).trans_lt d.isLt
  exact le_of_mul_le_mul_left actual mpos

def priceCeiling (c : Row n) (m : ℕ) : ℚ≥0 := (m : ℚ≥0)*∑ v, raw c v

def massCeiling (n m : ℕ) : ℚ≥0 := (m : ℚ≥0)*(n : ℚ≥0)

def pairs (c : Row n) (m : ℕ) : List (ℚ≥0 × ℚ≥0) :=
  (grid (floorPrice c) (priceCeiling c m)).flatMap fun B =>
    (grid 1 (massCeiling n m)).map fun U => (B,U)

def reprice (c : Row n) (B U : ℚ≥0) : Row n :=
  Vector.ofFn fun v => (BinaryRawRational.encode
    (Code.ofNNRat (raw c v/B+1/U))).1

theorem reprice_eq (c : Row n) (B U : ℚ≥0) (v : Fin n) :
    weights (reprice c B U) v = weights c v/(B : ℝ≥0)+1/(U : ℝ≥0) := by
  rcases v with ⟨v,hi⟩
  have code : raw (reprice c B U) ⟨v,hi⟩ = raw c ⟨v,hi⟩/B+1/U := by
    change (BinaryRational.decode (reprice c B U)[v]).value = _
    simp only [reprice,Vector.getElem_ofFn,BinaryRawRational.encode_value,Code.value_ofNNRat]
  rw [← raw_eq,code]
  simp only [NNRat.cast_add,NNRat.cast_div,NNRat.cast_one,raw_eq]

theorem reprice_cost (c : Row n) (B U : ℚ≥0) (w : Fin n → ℝ≥0) :
    weightedCost (weights (reprice c B U)) w =
      weightedCost (weights c) w/(B : ℝ≥0)+totalWeight w/(U : ℝ≥0) := by
  simp only [weightedCost,totalWeight,Finset.sum_div,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [reprice_eq]
  simp only [div_eq_mul_inv]
  ring

def candidate (hn : 0 < n) (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m) (B U : ℚ≥0) : Row n :=
  ConcurrentVertexCover.solve hn A (reprice c B U) P

theorem candidate_bounds (hn : 0 < n) (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    (B U : ℚ≥0) (Bpos : 0 < B) (Upos : 0 < U)
    (reach : ∀ i : Fin m, Nonempty (SimplePath (graph A) (P.get i).1 (P.get i).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) (noArc : ¬ (graph A).Adj (P.get d).1 (P.get d).2)
    (w : Fin n → ℝ≥0) (normal : (m : ℝ≥0) ≤ ∑ i, demandDistance (graph A) w (P.get i))
    (fitsPrice : weightedCost (weights c) w ≤ (B : ℝ≥0)) (fitsMass : totalWeight w ≤ (U : ℝ≥0)) :
    let z := weights (candidate hn A c P B U)
    ((m : ℝ≥0) ≤ ∑ i, demandDistance (graph A) z (P.get i)) ∧
      weightedCost (weights c) z ≤ 6*(B : ℝ≥0) ∧ totalWeight z ≤ 6*(U : ℝ≥0) := by
  let z := weights (candidate hn A c P B U)
  have bp : (0 : ℝ≥0) < B := by exact_mod_cast Bpos
  have up : (0 : ℝ≥0) < U := by exact_mod_cast Upos
  have allPositive (v : Fin n) : 0 < weights (reprice c B U) v := by
    rw [reprice_eq]
    exact add_pos_of_nonneg_of_pos zero_le (div_pos zero_lt_one up)
  obtain ⟨valid,paid⟩ := ConcurrentVertexCover.solve_spec hn A (reprice c B U) P
    allPositive reach d different noArc w normal
  have mixed : weightedCost (weights (reprice c B U)) w ≤ 2 := by
    rw [reprice_cost]
    exact (add_le_add ((div_le_one₀ bp).mpr fitsPrice) ((div_le_one₀ up).mpr fitsMass)).trans_eq (by norm_num)
  have bound : weightedCost (weights (reprice c B U)) z ≤ 6 := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_ofNat]
    exact paid.trans ((mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr mixed) (by norm_num)).trans_eq (by norm_num))
  rw [reprice_cost] at bound
  refine ⟨valid,(div_le_iff₀ bp).mp ?_,(div_le_iff₀ up).mp ?_⟩
  · exact (le_add_of_nonneg_right zero_le).trans bound
  · exact (le_add_of_nonneg_left zero_le).trans bound

end DirectedFlowCutGap.ConcurrentVertexBudget
