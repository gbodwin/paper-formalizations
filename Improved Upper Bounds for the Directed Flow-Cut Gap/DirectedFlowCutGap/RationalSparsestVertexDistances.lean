import DirectedFlowCutGap.RationalSparsestEdgeDistances
import DirectedFlowCutGap.FractionalCoverGraphOracle
import DirectedFlowCutGap.SparsestVertexBridge

/-! Compute rational vertex distances with the binary path engine.
A departure from the demand source costs zero and a departure from an
internal vertex costs its original length. -/
namespace DirectedFlowCutGap.RationalSparsestVertexDistances

open scoped BigOperators NNReal NNRat ENNReal
open BinaryFractionalWalkOracle (Adjacency graph)
open BinaryFractionalRows (Row)
open BinaryRational (decode zero)
open FractionalCoverRawCore (rational)

noncomputable def weights {n : ℕ} (w : Row n) (v : Fin n) : ℝ≥0 :=
  ((decode w[v.val]).value : ℝ≥0)

def outgoing {n : ℕ} (w : Row n) (s : Fin n) : RationalEdgeThresholds.Weights n :=
  Vector.ofFn fun u => Vector.replicate n (if u = s then zero else w[u.val])

private def values {n : ℕ} (w : Row n) : FractionalCover.Row n :=
  Vector.ofFn fun i => rational (decode w[i.val])

private theorem value_eq {n : ℕ} (w : Row n) (v : Fin n) :
    ((FractionalCover.value (values w) v : ℚ) : ℝ) = (weights w v : ℝ) := by
  simp only [values, FractionalCover.value_ofFn, weights, rational]
  rfl

private theorem departure {n : ℕ} (w : Row n) (s : Fin n) (e : Fin n × Fin n) :
    (RationalEdgeThresholds.weights (outgoing w s) e : ℝ) =
      (FractionalCoverGraphOracle.outgoing (values w) s e : ℝ) := by
  rcases e with ⟨u,v⟩
  have test : (⟨u.val,u.isLt⟩ : Fin n) = u := Fin.eta u _
  simp only [RationalEdgeThresholds.weights, RationalEdgeThresholds.cost,
    BinaryFractionalWalkOracle.decodeCost, outgoing, Vector.getElem_ofFn, Vector.getElem_replicate,
    test, FractionalCoverGraphOracle.outgoing]
  by_cases source : u = s
  · simp [source, RawNonnegativeRational.Code.value_zero]
  · rw [ite_eq_right source, ite_eq_right source]
    exact (value_eq w u).symm

theorem path_weight {n : ℕ} {G : Digraph (Fin n)} {s t : Fin n}
    (w : Row n) (p : SimplePath G s t) :
    p.edgeWeight (RationalEdgeThresholds.weights (outgoing w s)) = p.weight (weights w) := by
  apply NNReal.coe_injective
  simp only [SimplePath.edgeWeight, SimplePath.weight, NNReal.coe_sum, departure]
  have relation := congrArg (fun r : ℚ => (r : ℝ)) (FractionalCoverGraphOracle.outgoing_pathCost p (values w))
  simpa only [FractionalCoverWalkOracle.pathCost, FractionalCover.length, Rat.cast_sum, value_eq] using relation

theorem distance_transfer {n : ℕ} (A : Adjacency n) (w : Row n) (s t : Fin n) :
    edgeDistance (graph A) (RationalEdgeThresholds.weights (outgoing w s)) s t =
      vertexDistance (graph A) (weights w) s t := by
  unfold edgeDistance vertexDistance
  apply iInf_congr
  intro p
  rw [path_weight w p]

def distance {n : ℕ} (A : Adjacency n) (w : Row n) (e : Fin n × Fin n) : Option ℚ≥0 :=
  RationalSparsestEdgeDistances.distance A (outgoing w e.1) e

theorem distance_exact {n : ℕ} (A : Adjacency n) (w : Row n) (e : Fin n × Fin n) :
    RationalSparsestEdgeDistances.observe (distance A w e) =
      vertexDistance (graph A) (weights w) e.1 e.2 := by
  rw [distance, RationalSparsestEdgeDistances.distance_exact, distance_transfer]

theorem none_iff {n : ℕ} (A : Adjacency n) (w : Row n) (e : Fin n × Fin n) :
    distance A w e = none ↔ vertexDistance (graph A) (weights w) e.1 e.2 = ⊤ := by
  rw [distance, ← distance_transfer]
  exact RationalSparsestEdgeDistances.none_iff _ _ _

theorem finite_value {n : ℕ} (A : Adjacency n) (w : Row n) (e : Fin n × Fin n)
    {d : ℚ≥0} (found : distance A w e = some d) :
    (d : ℝ≥0) = SparsestVertexBridge.demandDistance (graph A) (weights w) e := by
  have h := distance_exact A w e
  rw [found] at h
  unfold SparsestVertexBridge.demandDistance
  rw [← h]
  rfl

end DirectedFlowCutGap.RationalSparsestVertexDistances
