import DirectedFlowCutGap.MeasuredCanonicalPathInputs

/-! Scale the best recorded covering row by the number of demands, then
emit the exact original canonical edge matrix or vertex row. -/
namespace DirectedFlowCutGap.MeasuredCoverLengths

open FractionalCoverRawCore (RawRow RowBounded decodeRow rational)
open FractionalCover (Row value value_ofFn)
open MeasuredBudgetPrices (tabulate canonical canonicalWork)
open MeasuredCanonicalPathInputs (matrix)
open RawNonnegativeRational (Code)
open RationalEdgeThresholds (Weights)

variable {r n : ℕ}

def scale (m : ℕ) (y : RawRow r) : RawRow r × ℕ :=
  tabulate fun i => BinaryRawRational.mul (Code.ofNat m) (FractionalCoverRawCore.get y i)

theorem scale_value (m : ℕ) (y : RawRow r) :
    decodeRow (scale m y).1 = Vector.ofFn fun i => (m : ℚ)*value (decodeRow y) i := by
  apply Vector.ext
  intro i hi
  simp only [scale,decodeRow,FractionalCoverRawCore.get,Vector.getElem_ofFn,
    MeasuredBudgetPrices.tabulate_value,BinaryRawRational.mul_value,FractionalCoverRawCore.rational_mul,
    FractionalCoverRawCore.rational_nat,value_ofFn]

theorem scale_bounds (m : ℕ) (y : RawRow r) {W : ℕ} (fit : RowBounded y W) :
    RowBounded (scale m y).1 (m+W) ∧ (scale m y).2 ≤ r*BinaryRawRational.budget (m+W) := by
  have dimension : (Code.ofNat m).Bounded m := MeasuredMultiplicityUpdate.ofNat_fits Nat.lt_two_pow_self.le
  constructor
  · intro i
    simp only [FractionalCoverRawCore.get,scale,MeasuredBudgetPrices.tabulate_value,
      BinaryRawRational.mul_value]
    exact Code.bounded_mul dimension (fit i)
  · exact MeasuredBudgetPrices.tabulate_charge _ fun i =>
      BinaryRawRational.mul_paid (Code.bounded_mono dimension (Nat.le_add_right ..))
        (Code.bounded_mono (fit i) (Nat.le_add_left ..))

def canonicalRow (y : RawRow r) : BinaryFractionalRows.Row r × ℕ :=
  tabulate fun i => canonical (FractionalCoverRawCore.get y i)

theorem canonicalRow_value (y : RawRow n) :
    (canonicalRow y).1 = ConcurrentVertexCover.encoded (decodeRow y) := by
  apply Vector.ext
  intro i hi
  simp only [canonicalRow,MeasuredBudgetPrices.tabulate_value,MeasuredBudgetPrices.canonical_value,
    ConcurrentVertexCover.encoded,Vector.getElem_ofFn,FractionalCoverRawCore.decode_value]
  congr 2
  apply congrArg Code.ofNNRat
  apply Subtype.ext
  exact (max_eq_left (FractionalCoverRawCore.rational_nonneg _)).symm

theorem canonicalRow_charge (y : RawRow r) {W : ℕ} (fit : RowBounded y W) :
    (canonicalRow y).2 ≤ r*canonicalWork W :=
  MeasuredBudgetPrices.tabulate_charge _ fun i => (MeasuredBudgetPrices.canonical_bounds (fit i)).2

def edge (m : ℕ) (y : RawRow (n*n)) : Weights n × ℕ :=
  let scaled := scale m y
  let packed := matrix scaled.1
  (packed.1,scaled.2+packed.2)

theorem edge_value (m : ℕ) (y : RawRow (n*n)) :
    (edge m y).1 = ConcurrentEdgeOracle.encoded (Vector.ofFn fun i => (m : ℚ)*value (decodeRow y) i) := by
  simp only [edge,MeasuredCanonicalPathInputs.matrix_value,scale_value]

def vertex (m : ℕ) (y : RawRow n) : BinaryFractionalRows.Row n × ℕ :=
  let scaled := scale m y
  let packed := canonicalRow scaled.1
  (packed.1,scaled.2+packed.2)

theorem vertex_value (m : ℕ) (y : RawRow n) :
    (vertex m y).1 = ConcurrentVertexCover.encoded (Vector.ofFn fun i => (m : ℚ)*value (decodeRow y) i) := by
  simp only [vertex,canonicalRow_value,scale_value]

def work (r m W : ℕ) : ℕ :=
  r*BinaryRawRational.budget (m+W)+r*canonicalWork (m+W)

theorem edge_charge (m : ℕ) (y : RawRow (n*n)) {W : ℕ} (fit : RowBounded y W) :
    (edge m y).2 ≤ work (n*n) m W := by
  obtain ⟨stored,fee⟩ := scale_bounds m y fit
  exact Nat.add_le_add fee (MeasuredCanonicalPathInputs.matrix_charge (scale m y).1 stored)

theorem vertex_charge (m : ℕ) (y : RawRow n) {W : ℕ} (fit : RowBounded y W) :
    (vertex m y).2 ≤ work n m W := by
  obtain ⟨stored,fee⟩ := scale_bounds m y fit
  exact Nat.add_le_add fee (canonicalRow_charge (scale m y).1 stored)

end DirectedFlowCutGap.MeasuredCoverLengths
