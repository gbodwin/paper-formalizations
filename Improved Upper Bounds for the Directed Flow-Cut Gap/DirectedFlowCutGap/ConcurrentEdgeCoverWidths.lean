import DirectedFlowCutGap.MultiplicityCoverWidths
import DirectedFlowCutGap.ConcurrentEdgeMassBudget

/-! Bound the actual rational covering state and encoded length matrices
from the binary price matrix and the number of supplied demands. -/
namespace DirectedFlowCutGap.ConcurrentEdgeCoverWidths

open scoped BigOperators NNRat
open BinaryRational (StoredBounded)
open BinaryFractionalRows (stored_raw_bound)
open BinaryFractionalWalkOracle (Adjacency decodeCost)
open RationalEdgeThresholds (Weights cost)
open ConcurrentEdgeOracle (Edge Resource edge resource)
open FractionalCover (Row value value_ofFn)
open MultiplicityCoverWidths (Fits fits_code fits_mul fits_nat RowFits ColumnFits StateFits weightWidth normalizedWidth)
open RawNonnegativeRational (Code)

variable {m n : ℕ}

def MatrixFits (a : Weights n) (B : ℕ) : Prop :=
  ∀ u v : Fin n, StoredBounded a[u.val][v.val] B

theorem rawPrice_fits (c : Weights n) {B : ℕ} (fit : MatrixFits c B) (e : Edge n) :
    NNRatStoredBounds.Bounded (ConcurrentEdgeZeroPrices.rawPrice c e) B :=
  NNRatStoredBounds.value_bounded (stored_raw_bound (fit e.1 e.2))

theorem priceRow_fits (A : Adjacency n) (c : Weights n) {B : ℕ} (fit : MatrixFits c B) :
    RowFits (ConcurrentEdgeCover.priceRow A c) B := by
  intro i
  let e := edge i
  have equation : value (ConcurrentEdgeCover.priceRow A c) i =
      if A[e.1.val][e.2.val] then FractionalCoverRawCore.rational (decodeCost (cost c) e) else 1 := by
    simp only [ConcurrentEdgeCover.priceRow,value_ofFn,e]
  rw [equation]
  split
  · exact fits_code (stored_raw_bound (fit e.1 e.2))
  · exact fits_nat (a := 1) (B := B) (Nat.one_le_pow _ _ (by decide))

theorem oracle_columns (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m) (c : Row (n*n))
    (y : Row (n*n)) : ColumnFits (ConcurrentEdgeOracle.oracle hn A P c y).column m := by
  intro i
  have h : MultiplicityCover.coeff (ConcurrentEdgeOracle.oracle hn A P c y).column i ≤ m := by
    simp only [ConcurrentEdgeOracle.oracle,ConcurrentEdgeOracle.column,MultiplicityCover.coeff,Vector.getElem_ofFn]
    calc
      _ ≤ ∑ _j : Fin m, (1 : ℕ) := by
        apply Finset.sum_le_sum
        intro j _
        split <;> decide
      _ = m := by simp
  exact h.trans Nat.lt_two_pow_self.le

theorem solve_state_fits (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {B : ℕ} (fit : MatrixFits c B) :
    let prices := ConcurrentEdgeCover.priceRow A c
    let oracle := ConcurrentEdgeOracle.oracle hn A P prices
    StateFits (MultiplicityCover.solve prices oracle) B m (3*(n*n)^2) :=
  MultiplicityCoverWidths.solve_fits _ _ (priceRow_fits A c fit) (oracle_columns hn A P _)

theorem encoded_fits (y : Row (n*n)) {B : ℕ} (fit : RowFits y B) :
    MatrixFits (ConcurrentEdgeOracle.encoded y) (B+1) := by
  intro u v
  have exactValue := fit (resource (u,v))
  obtain ⟨q,read,bounded⟩ := exactValue
  have nonnegative : 0 ≤ value y (resource (u,v)) := by rw [← read]; exact q.property
  have canon : (⟨max (value y (resource (u,v))) 0,le_max_right _ _⟩ : ℚ≥0) = q := by
    apply Subtype.ext
    change max (value y (resource (u,v))) 0 = (q : ℚ)
    rw [max_eq_left nonnegative,read]
  simp only [ConcurrentEdgeOracle.encoded,Vector.getElem_ofFn]
  apply BinaryRawRational.encode_width
  change (Code.ofNNRat (⟨max (value y (resource (u,v))) 0,le_max_right _ _⟩ : ℚ≥0)).Bounded B
  rw [canon]
  exact bounded

def outputWidth (n m B : ℕ) : ℕ :=
  m+normalizedWidth (n*n) m (weightWidth (n*n) B m (3*(n*n)^2))+1

theorem solve_fits (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {B : ℕ} (fit : MatrixFits c B) :
    MatrixFits (ConcurrentEdgeCover.solve hn A c P) (outputWidth n m B) := by
  have run := (solve_state_fits hn A c P fit).best
  apply encoded_fits
  intro i
  simp only [value_ofFn]
  exact fits_mul (fits_nat (a := m) (B := m) Nat.lt_two_pow_self.le) (run i)

theorem reprice_fits (c : Weights n) (B U : ℚ≥0) {L R S : ℕ}
    (input : MatrixFits c L) (fee : NNRatStoredBounds.Bounded B R) (mass : NNRatStoredBounds.Bounded U S) :
    MatrixFits (ConcurrentEdgeMassBudget.reprice c B U) (L+R+S+2) := by
  intro u v
  simp only [ConcurrentEdgeMassBudget.reprice,Vector.getElem_ofFn]
  apply BinaryRawRational.encode_width
  have ingredients := NNRatStoredBounds.add_bounded
    (NNRatStoredBounds.div_bounded (rawPrice_fits c input (u,v)) fee)
    (NNRatStoredBounds.div_bounded NNRatStoredBounds.one_bounded mass)
  simpa only [Nat.zero_add] using ingredients

theorem budget_solve_fits (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (B U : ℚ≥0) {L R S : ℕ} (input : MatrixFits c L)
    (fee : NNRatStoredBounds.Bounded B R) (mass : NNRatStoredBounds.Bounded U S) :
    MatrixFits (ConcurrentEdgeMassBudget.solve hn A c P B U) (outputWidth n m (L+R+S+2)) :=
  solve_fits hn A _ P (reprice_fits c B U input fee mass)

end DirectedFlowCutGap.ConcurrentEdgeCoverWidths
