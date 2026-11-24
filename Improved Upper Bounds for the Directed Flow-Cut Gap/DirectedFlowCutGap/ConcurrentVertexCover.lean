import DirectedFlowCutGap.ConcurrentVertexOracle
import DirectedFlowCutGap.VertexNormalizedPotentials

/-! A bounded joint-path covering routine for normalized vertex lengths.
The positive-price routine compares with any real normalized assignment. -/
namespace DirectedFlowCutGap.ConcurrentVertexCover

open scoped BigOperators NNReal NNRat ENNReal
open BinaryFractionalWalkOracle (Adjacency graph)
open ConcurrentEdgeOracle (Edge Profile)
open RationalSparsestVertexDistances (weights)
open SparsestVertexBridge (demandDistance)
open FractionalCover (Row value value_ofFn objective)
open ConcurrentVertexOracle (oracle columns profileCoeff)

variable {m n : ℕ}

theorem normalization_iff (A : Adjacency n) (P : Vector (Edge n) m) (w : Fin n → ℝ≥0)
    (reach : ∀ i : Fin m, Nonempty (SimplePath (graph A) (P.get i).1 (P.get i).2))
    (target : ℝ≥0) :
    (target ≤ ∑ i : Fin m, demandDistance (graph A) w (P.get i)) ↔
      ∀ paths : Profile A P, target ≤ ∑ i : Fin m, (paths i).weight w := by
  constructor
  · intro normal paths
    refine normal.trans (Finset.sum_le_sum fun i _ => ?_)
    unfold demandDistance
    have finite := fun h => ((vertexDistance_eq_top_iff (graph A) w _ _).mp h) (reach i)
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal finite]
    exact vertexDistance_le_weight w (paths i)
  · intro all
    have smallest (i : Fin m) := vertexDistance_attained w (reach i)
    choose paths equal using smallest
    have read (i : Fin m) : demandDistance (graph A) w (P.get i) = (paths i).weight w := by
      simp only [demandDistance,equal,ENNReal.toNNReal_coe]
    simpa only [read] using all paths

def priceRow (c : BinaryFractionalRows.Row n) : Row n :=
  Vector.ofFn fun v => ((BinaryRational.decode (c.get v)).value : ℚ)

theorem price_read (c : BinaryFractionalRows.Row n) (v : Fin n) :
    (value (priceRow c) v : ℝ) = (weights c v : ℝ) := by
  cases v
  simp only [priceRow,value_ofFn,weights]
  rfl

private def rationalLength (a : ℚ) : ℚ≥0 := ⟨max a 0,le_max_right _ _⟩

def encoded (y : Row n) : BinaryFractionalRows.Row n :=
  Vector.ofFn fun v => (BinaryRawRational.encode
    (RawNonnegativeRational.Code.ofNNRat (rationalLength (value y v)))).1

theorem encoded_read (y : Row n) (nonneg : ∀ i, 0 ≤ value y i) (i : Fin n) :
    (weights (encoded y) i : ℝ) = (value y i : ℝ) := by
  rcases i with ⟨i,hi⟩
  have code : (BinaryRational.decode (encoded y)[i]).value = rationalLength (value y ⟨i,hi⟩) := by
    rw [encoded,Vector.getElem_ofFn,BinaryRawRational.encode_value]
    exact RawNonnegativeRational.Code.value_ofNNRat _
  change (((BinaryRational.decode (encoded y)[i]).value : ℝ≥0) : ℝ) = _
  rw [code]
  change ((max (value y ⟨i,hi⟩) 0 : ℚ) : ℝ) = _
  rw [max_eq_left (nonneg _)]

def base (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m) : Row n :=
  let prices := priceRow c
  (MultiplicityCover.solve prices (oracle hn A P prices)).best

def solve (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m) :
    BinaryFractionalRows.Row n :=
  encoded (Vector.ofFn fun v => (m : ℚ)*value (base hn A c P) v)

private theorem solve_read (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (positive : ∀ v, 0 ≤ value (base hn A c P) v) (v : Fin n) :
    (weights (solve hn A c P) v : ℝ) = (m : ℝ)*(value (base hn A c P) v : ℝ) := by
  unfold solve
  rw [encoded_read]
  · simp only [value_ofFn,Rat.cast_mul,Rat.cast_natCast]
  · intro i
    simp only [value_ofFn]
    exact mul_nonneg (by positivity) (positive i)

theorem solve_spec (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (positive : ∀ i, 0 < weights c i)
    (reach : ∀ i : Fin m, Nonempty (SimplePath (graph A) (P.get i).1 (P.get i).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) (noArc : ¬ (graph A).Adj (P.get d).1 (P.get d).2)
    (w : Fin n → ℝ≥0) (normal : (m : ℝ≥0) ≤ ∑ i : Fin m, demandDistance (graph A) w (P.get i)) :
    let z := weights (solve hn A c P)
    ((m : ℝ≥0) ≤ ∑ i : Fin m, demandDistance (graph A) z (P.get i)) ∧
      (weightedCost (weights c) z : ℝ) ≤ 3*(weightedCost (weights c) w : ℝ) := by
  let prices := priceRow c
  let pick := oracle hn A P prices
  let z := weights (solve hn A c P)
  have allPositive (i : Fin n) : 0 < value prices i := by
    have test : (0 : ℝ) < value prices i := by rw [price_read]; exact NNReal.coe_pos.mpr (positive i)
    exact_mod_cast test
  have valid := ConcurrentVertexOracle.oracle_correct hn A P prices reach d different noArc
  have state := MultiplicityCover.run_invariant prices (columns A P) pick hn allPositive valid
    (FractionalCover.fuel n)
  have baseFit : MultiplicityCover.Feasible (columns A P) (base hn A c P) := state.feasible
  have read := solve_read hn A c P baseFit.1
  have mpos : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_le _).trans_lt d.isLt
  constructor
  · apply (normalization_iff A P z reach _).mpr
    intro paths
    let column : MultiplicityCover.Column n := Vector.ofFn (profileCoeff A P paths)
    have eq (v : Fin n) : MultiplicityCover.coeff column v = profileCoeff A P paths v :=
      Vector.getElem_ofFn v.isLt
    have feasible := baseFit.2 column ⟨paths,eq⟩
    unfold MultiplicityCover.length at feasible
    rw [ConcurrentVertexOracle.profile_eval A P column paths eq] at feasible
    have real : (1 : ℝ) ≤ ∑ i : Fin m, ∑ v ∈ (paths i).internalVertices,
        (value (base hn A c P) v : ℝ) := by exact_mod_cast feasible
    apply NNReal.coe_le_coe.mp
    simp only [SimplePath.weight,NNReal.coe_sum,NNReal.coe_natCast,z,read]
    simpa only [mul_one,Finset.mul_sum] using mul_le_mul_of_nonneg_left real mpos.le
  · let compare (v : Fin n) := (w v : ℝ)/(m : ℝ)
    have comparison : MultiplicityCover.RealFeasible (columns A P) compare := by
      refine ⟨fun v => div_nonneg (NNReal.coe_nonneg _) mpos.le,?_⟩
      intro column member
      obtain ⟨paths,shape⟩ := member
      rw [ConcurrentVertexOracle.profile_eval A P column paths shape]
      unfold compare
      simp only [← Finset.sum_div]
      apply (le_div_iff₀ mpos).mpr
      have total := (normalization_iff A P w reach _).mp normal paths
      simpa only [one_mul,NNReal.coe_natCast,SimplePath.weight,NNReal.coe_sum] using NNReal.coe_le_coe.mpr total
    have approximate := MultiplicityCover.solve_three_approximation_real prices (columns A P) pick hn
      allPositive valid compare comparison
    have comparator :
        (∑ v, (value prices v : ℝ)*compare v) = (weightedCost (weights c) w : ℝ)/(m : ℝ) := by
      simp only [weightedCost,NNReal.coe_sum,NNReal.coe_mul,Finset.sum_div,prices,price_read,compare,mul_div_assoc]
    rw [comparator] at approximate
    have observed : (weightedCost (weights c) z : ℝ) =
        (m : ℝ)*(objective prices (base hn A c P) : ℝ) := by
      simp only [weightedCost,objective,NNReal.coe_sum,NNReal.coe_mul, Rat.cast_sum,Rat.cast_mul,
        Finset.mul_sum,z,read,prices,price_read]
      apply Finset.sum_congr rfl
      intro v _
      ring
    rw [observed]
    calc
      _ ≤ (m : ℝ)*(3*((weightedCost (weights c) w : ℝ)/(m : ℝ))) :=
        mul_le_mul_of_nonneg_left approximate mpos.le
      _ = _ := by field_simp [mpos.ne']

end DirectedFlowCutGap.ConcurrentVertexCover
