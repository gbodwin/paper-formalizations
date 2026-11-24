import DirectedFlowCutGap.MeasuredSparsitySelection
import DirectedFlowCutGap.MeasuredCanonicalCover
import DirectedFlowCutGap.ConcurrentVertexBudgetSelection

/-! Exact measured original cut prices and fractional masses for candidate
selection. Nonarcs contribute zero to the edge totals. -/
namespace DirectedFlowCutGap.MeasuredGraphPlanTotals

open scoped BigOperators NNRat
open BinaryFractionalWalkOracle (Adjacency decodeCost)
open BinaryRational (StoredBounded)
open ConcurrentEdgeOracle (Edge Resource edge resource)
open ConcurrentEdgeCoverWidths (MatrixFits)
open FractionalCoverRawCore (RawRow RowBounded decodeRow rational)
open FractionalCover (objective value)
open MeasuredSparsitySelection (Totals totals totals_price totals_mass totals_bounds)
open MeasuredMultiplicityForms (dotWork)
open MeasuredBudgetPrices (tabulate tabulate_value tabulate_charge)
open RationalEdgeThresholds (Weights cost)
open RationalEdgeDecomposition (originalWeight originalTotal)
open RawNonnegativeRational (Code)

variable {n : ℕ}

def arcValues (A : Adjacency n) (w : Weights n) : RawRow (n*n) × ℕ :=
  tabulate fun i =>
    let uv := edge i
    if A[uv.1.val][uv.2.val] then BinaryRawRational.decode ((cost w) uv).1 else (Code.zero,0)

theorem arcValues_value (A : Adjacency n) (w : Weights n) (e : Edge n) :
    value (decodeRow (arcValues A w).1) (resource e) = (originalWeight A w e : ℚ) := by
  simp only [FractionalCoverRawCore.decode_value,FractionalCoverRawCore.get,arcValues,tabulate_value,
    Fin.eta,ConcurrentEdgeOracle.edge_resource,originalWeight]
  split
  · rw [BinaryRawRational.decode_value]
    rfl
  · exact FractionalCoverRawCore.rational_zero

theorem arcValues_bounds (A : Adjacency n) (w : Weights n) {B : ℕ} (fit : MatrixFits w B) :
    RowBounded (arcValues A w).1 B ∧ (arcValues A w).2 ≤ (n*n)*(40*(B+1)^2) := by
  constructor
  · intro i
    simp only [FractionalCoverRawCore.get,arcValues,tabulate_value,Fin.eta]
    split
    · rw [BinaryRawRational.decode_value]
      exact BinaryFractionalRows.stored_raw_bound (fit (edge i).1 (edge i).2)
    · exact Code.bounded_mono Code.bounded_zero (Nat.zero_le B)
  · apply tabulate_charge
    intro i
    dsimp only
    split
    · exact BinaryRawRational.decode_paid (fit (edge i).1 (edge i).2)
    · exact Nat.zero_le _

def edgeTotals (A : Adjacency n) (c w : Weights n) : Totals :=
  let fees := arcValues A c
  let lengths := arcValues A w
  let read := totals fees.1 lengths.1
  {read with charge := fees.2+lengths.2+read.charge}

theorem edgeTotals_value (A : Adjacency n) (c w : Weights n) :
    (edgeTotals A c w).price.value = ConcurrentEdgeBudgetSelection.rawCost A c w ∧
      (edgeTotals A c w).mass.value = originalTotal A w := by
  let fees := (arcValues A c).1
  let lengths := (arcValues A w).1
  constructor
  · apply Subtype.ext
    change rational (totals fees lengths).price = (ConcurrentEdgeBudgetSelection.rawCost A c w : ℚ)
    rw [totals_price,objective,← (finProdFinEquiv : Edge n ≃ Resource n).sum_comp
      (fun i => value (decodeRow fees) i * value (decodeRow lengths) i)]
    change (∑ e : Edge n, value (decodeRow fees) (resource e) * value (decodeRow lengths) (resource e)) = _
    simp only [fees,lengths,arcValues_value,ConcurrentEdgeBudgetSelection.rawCost,NNRat.cast_sum,NNRat.coe_mul]
  · apply Subtype.ext
    change rational (totals fees lengths).mass = (originalTotal A w : ℚ)
    rw [totals_mass,← (finProdFinEquiv : Edge n ≃ Resource n).sum_comp (value (decodeRow lengths))]
    change (∑ e : Edge n, value (decodeRow lengths) (resource e)) = _
    simp only [lengths,arcValues_value,originalTotal,NNRat.cast_sum]

def totalsWork (r B W : ℕ) : ℕ := r*(40*(B+1)^2)+r*(40*(W+1)^2)+dotWork r B W+dotWork r 0 W

theorem edgeTotals_bounds (A : Adjacency n) (c w : Weights n) {B W : ℕ}
    (price : MatrixFits c B) (lengths : MatrixFits w W) :
    let z := edgeTotals A c w
    z.price.Bounded ((n*n)*(B+W+1)) ∧ z.mass.Bounded ((n*n)*(W+1)) ∧ z.charge ≤ totalsWork (n*n) B W := by
  obtain ⟨feeFit,feeWork⟩ := arcValues_bounds A c price
  obtain ⟨lengthFit,lengthWork⟩ := arcValues_bounds A w lengths
  obtain ⟨f,m,paid⟩ := totals_bounds _ _ feeFit lengthFit
  refine ⟨f,m,?_⟩
  simpa only [edgeTotals,totalsWork,Nat.add_assoc] using Nat.add_le_add (Nat.add_le_add feeWork lengthWork) paid

def vertexTotals (c w : BinaryFractionalRows.Row n) : Totals :=
  let fees := MeasuredCanonicalCover.readVertex c
  let lengths := MeasuredCanonicalCover.readVertex w
  let read := totals fees.1 lengths.1
  {read with charge := fees.2+lengths.2+read.charge}

private theorem vertex_read (c : BinaryFractionalRows.Row n) (i : Fin n) :
    value (decodeRow (MeasuredCanonicalCover.readVertex c).1) i = (ConcurrentVertexBudget.raw c i : ℚ) := by
  simp only [MeasuredCanonicalCover.readVertex_value,MeasuredConcurrentCover.vertexPrices,
    FractionalCoverRawCore.decode_value,FractionalCoverRawCore.get_ofFn,ConcurrentVertexBudget.raw,rational]

theorem vertexTotals_value (c w : BinaryFractionalRows.Row n) :
    (vertexTotals c w).price.value = ConcurrentVertexBudgetSelection.rawCost c w ∧
      (vertexTotals c w).mass.value = ConcurrentVertexBudgetSelection.rawMass w := by
  constructor
  · apply Subtype.ext
    change rational (totals (MeasuredCanonicalCover.readVertex c).1
      (MeasuredCanonicalCover.readVertex w).1).price = (ConcurrentVertexBudgetSelection.rawCost c w : ℚ)
    simp only [totals_price,objective,vertex_read,ConcurrentVertexBudgetSelection.rawCost,NNRat.cast_sum,NNRat.coe_mul]
  · apply Subtype.ext
    change rational (totals (MeasuredCanonicalCover.readVertex c).1
      (MeasuredCanonicalCover.readVertex w).1).mass = (ConcurrentVertexBudgetSelection.rawMass w : ℚ)
    simp only [totals_mass,vertex_read,ConcurrentVertexBudgetSelection.rawMass,NNRat.cast_sum]

theorem vertexTotals_bounds (c w : BinaryFractionalRows.Row n) {B W : ℕ}
    (price : ∀ i, StoredBounded (c.get i) B) (lengths : ∀ i, StoredBounded (w.get i) W) :
    let z := vertexTotals c w
    z.price.Bounded (n*(B+W+1)) ∧ z.mass.Bounded (n*(W+1)) ∧ z.charge ≤ totalsWork n B W := by
  have feeFit : RowBounded (MeasuredCanonicalCover.readVertex c).1 B := by
    rw [MeasuredCanonicalCover.readVertex_value]
    exact MeasuredConcurrentCover.vertexPrices_fits c price
  have lengthFit : RowBounded (MeasuredCanonicalCover.readVertex w).1 W := by
    rw [MeasuredCanonicalCover.readVertex_value]
    exact MeasuredConcurrentCover.vertexPrices_fits w lengths
  obtain ⟨f,m,paid⟩ := totals_bounds _ _ feeFit lengthFit
  refine ⟨f,m,?_⟩
  have readPrice := MeasuredCanonicalCover.readVertex_charge c price
  have readLengths := MeasuredCanonicalCover.readVertex_charge w lengths
  simpa only [vertexTotals,totalsWork,Nat.add_assoc] using Nat.add_le_add (Nat.add_le_add readPrice readLengths) paid

end DirectedFlowCutGap.MeasuredGraphPlanTotals
