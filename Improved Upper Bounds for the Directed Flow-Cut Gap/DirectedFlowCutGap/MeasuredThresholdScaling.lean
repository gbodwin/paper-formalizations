import DirectedFlowCutGap.MeasuredSparsestThreshold
import DirectedFlowCutGap.RationalSparsestVertexRound

/-! Canonicalize the selected threshold once, then divide the actual length
fields in binary. Reproduce the exact raw rounding input of the reference. -/
namespace DirectedFlowCutGap.MeasuredThresholdScaling

open BinaryFractionalWalkOracle (Adjacency)
open BinaryRational (Fraction StoredBounded)
open ConcurrentEdgeCoverWidths (MatrixFits)
open RationalEdgeThresholds (Weights)
open RawNonnegativeRational (Code)
open MeasuredBudgetPrices (tabulate tabulate_value tabulate_charge)
open BinaryRationalNormalize (normalize normalize_value normalize_width normalize_paid)

variable {n : ℕ}

private def length (a : Fraction) (threshold : Code) : Code × ℕ :=
  let read := BinaryRawRational.decode a
  let scaled := BinaryRawRational.div read.1 threshold
  (scaled.1,read.2+scaled.2)

private theorem length_value (a : Fraction) (threshold : Code) :
    (length a threshold).1 = (BinaryRational.decode a).div threshold := by
  simp only [length,BinaryRawRational.decode_value,BinaryRawRational.div_value]

private def lengthWork (B T : ℕ) : ℕ := 40*(B+1)^2+BinaryRawRational.budget (max B T)

private theorem length_charge (a : Fraction) (threshold : Code) {B T : ℕ}
    (fits : StoredBounded a B) (bounded : threshold.Bounded T) :
    (length a threshold).2 ≤ lengthWork B T := by
  have decoded : (BinaryRawRational.decode a).1.Bounded B := by
    rw [BinaryRawRational.decode_value]
    exact BinaryFractionalRows.stored_raw_bound fits
  exact Nat.add_le_add (BinaryRawRational.decode_paid fits)
    (BinaryRawRational.div_paid (Code.bounded_mono decoded (le_max_left ..))
      (Code.bounded_mono bounded (le_max_right ..)))

def edge (A : Adjacency n) (w c : Weights n) (threshold : Code) : EncodedEdgeGadget.Input n × ℕ :=
  let normalized := normalize threshold
  let lengths := tabulate fun u => tabulate fun v => length ((w.get u).get v) normalized.1
  let prices := tabulate fun u => tabulate fun v => BinaryRawRational.decode ((c.get u).get v)
  (⟨A,lengths.1,prices.1⟩,normalized.2+lengths.2+prices.2)

theorem edge_value (A : Adjacency n) (w c : Weights n) (threshold : Code) :
    (edge A w c threshold).1 = RationalSparsestEdgeRound.scaled A w c threshold.value := by
  have lengths : (tabulate fun u => tabulate fun v => length ((w.get u).get v) (normalize threshold).1).1 =
      w.map (fun row => row.map fun q => (BinaryRational.decode q).div (Code.ofNNRat threshold.value)) := by
    apply Vector.ext
    intro u hu
    apply Vector.ext
    intro v hv
    simp only [tabulate_value,Vector.getElem_map,length_value,normalize_value]
    rfl
  have prices : (tabulate fun u => tabulate fun v => BinaryRawRational.decode ((c.get u).get v)).1 =
      c.map (fun row => row.map BinaryRational.decode) := by
    apply Vector.ext
    intro u hu
    apply Vector.ext
    intro v hv
    simp only [tabulate_value,Vector.getElem_map,BinaryRawRational.decode_value]
    rfl
  simp only [edge,RationalSparsestEdgeRound.scaled,lengths,prices]

def work (r B C T : ℕ) : ℕ :=
  BinaryRationalNormalize.budget T+r*lengthWork B T+r*(40*(C+1)^2)

theorem edge_charge (A : Adjacency n) (w c : Weights n) (threshold : Code) {B C T : ℕ}
    (lengths : MatrixFits w B) (prices : MatrixFits c C) (bound : threshold.Bounded T) :
    (edge A w c threshold).2 ≤ work (n*n) B C T := by
  have checked := normalize_width bound
  have scaled : (tabulate fun u => tabulate fun v => length ((w.get u).get v) (normalize threshold).1).2
      ≤ n*n*lengthWork B T := by
    rw [Nat.mul_assoc]
    exact tabulate_charge _ fun u => tabulate_charge _ fun v => length_charge _ _ (lengths u v) checked
  have receipt : (tabulate fun u => tabulate fun v => BinaryRawRational.decode ((c.get u).get v)).2
      ≤ n*n*(40*(C+1)^2) := by
    rw [Nat.mul_assoc]
    exact tabulate_charge _ fun u => tabulate_charge _ fun v => BinaryRawRational.decode_paid (prices u v)
  exact Nat.add_le_add (Nat.add_le_add (normalize_paid bound) scaled) receipt

def vertex (A : Adjacency n) (w c : BinaryFractionalRows.Row n) (threshold : Code) :
    EncodedUnitCostReplication.Input n × ℕ :=
  let normalized := normalize threshold
  let lengths := tabulate fun u => length (w.get u) normalized.1
  let prices := tabulate fun u => BinaryRawRational.decode (c.get u)
  (⟨A,lengths.1,prices.1⟩,normalized.2+lengths.2+prices.2)

theorem vertex_value (A : Adjacency n) (w c : BinaryFractionalRows.Row n) (threshold : Code) :
    (vertex A w c threshold).1 = RationalSparsestVertexRound.scaled A w c threshold.value := by
  have lengths : (tabulate fun u => length (w.get u) (normalize threshold).1).1 =
      w.map (fun q => (BinaryRational.decode q).div (Code.ofNNRat threshold.value)) := by
    apply Vector.ext
    intro u hu
    simp only [tabulate_value,Vector.getElem_map,length_value,normalize_value]
    rfl
  have prices : (tabulate fun u => BinaryRawRational.decode (c.get u)).1 = c.map BinaryRational.decode := by
    apply Vector.ext
    intro u hu
    simp only [tabulate_value,Vector.getElem_map,BinaryRawRational.decode_value]
    rfl
  simp only [vertex,RationalSparsestVertexRound.scaled,lengths,prices]

theorem vertex_charge (A : Adjacency n) (w c : BinaryFractionalRows.Row n) (threshold : Code) {B C T : ℕ}
    (lengths : ∀ i, StoredBounded (w.get i) B) (prices : ∀ i, StoredBounded (c.get i) C)
    (bound : threshold.Bounded T) : (vertex A w c threshold).2 ≤ work n B C T := by
  have scaled := tabulate_charge (fun u => length (w.get u) (normalize threshold).1) (fun u =>
    length_charge _ _ (lengths u) (normalize_width bound))
  have receipt := tabulate_charge (fun u => BinaryRawRational.decode (c.get u)) (fun u =>
    BinaryRawRational.decode_paid (prices u))
  exact Nat.add_le_add (Nat.add_le_add (normalize_paid bound) scaled) receipt

end DirectedFlowCutGap.MeasuredThresholdScaling
