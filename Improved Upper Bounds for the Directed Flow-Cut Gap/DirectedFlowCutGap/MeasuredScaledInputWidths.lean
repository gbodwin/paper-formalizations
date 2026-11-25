import DirectedFlowCutGap.MeasuredThresholdScaling
import DirectedFlowCutGap.BinaryEdgeGadget

/-! Propagate stored price and length widths through one exact threshold rescaling. -/
namespace DirectedFlowCutGap.MeasuredScaledInputWidths

open BinaryFractionalWalkOracle (Adjacency)
open BinaryRational (StoredBounded)
open ConcurrentEdgeCoverWidths (MatrixFits)
open RationalEdgeThresholds (Weights)
open RawNonnegativeRational (Code)

variable {n : ℕ}

def width (length price threshold : ℕ) : ℕ := max (length+threshold) price

private theorem scaledLength {a : BinaryRational.Fraction} {q : Code} {B C T : ℕ}
    (fits : StoredBounded a B) (threshold : q.Bounded T) :
    ((BinaryRational.decode a).div (Code.ofNNRat q.value)).Bounded (width B C T) := by
  have normal := BinaryRationalNormalize.normalize_width threshold
  rw [BinaryRationalNormalize.normalize_value] at normal
  exact Code.bounded_mono (Code.bounded_div (BinaryFractionalRows.stored_raw_bound fits) normal)
    (le_max_left ..)

theorem edge (A : Adjacency n) (w c : Weights n) (q : Code) {B C T : ℕ}
    (lens : MatrixFits w B) (prices : MatrixFits c C) (threshold : q.Bounded T) :
    BinaryEdgeGadget.InputFits (MeasuredThresholdScaling.edge A w c q).1 (width B C T) := by
  rw [MeasuredThresholdScaling.edge_value]
  constructor
  · intro u v
    simp only [RationalSparsestEdgeRound.scaled,Vector.getElem_map]
    exact scaledLength (lens u v) threshold
  · intro u v
    simp only [RationalSparsestEdgeRound.scaled,Vector.getElem_map]
    exact Code.bounded_mono (BinaryFractionalRows.stored_raw_bound (prices u v)) (le_max_right ..)

theorem vertex (A : Adjacency n) (w c : BinaryFractionalRows.Row n) (q : Code) {B C T : ℕ}
    (lens : ∀ i, StoredBounded (w.get i) B) (prices : ∀ i, StoredBounded (c.get i) C)
    (threshold : q.Bounded T) :
    VertexReductionWidths.InputFits (MeasuredThresholdScaling.vertex A w c q).1 (width B C T) := by
  rw [MeasuredThresholdScaling.vertex_value]
  constructor
  · intro u
    simp only [RationalSparsestVertexRound.scaled,Vector.getElem_map]
    exact scaledLength (lens u) threshold
  · intro u
    simp only [RationalSparsestVertexRound.scaled,Vector.getElem_map]
    exact Code.bounded_mono (BinaryFractionalRows.stored_raw_bound (prices u)) (le_max_right ..)

end DirectedFlowCutGap.MeasuredScaledInputWidths
