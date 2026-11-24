import DirectedFlowCutGap.BinaryRationalNormalize
import DirectedFlowCutGap.ConcurrentVertexBudget
import DirectedFlowCutGap.ConcurrentEdgeCoverWidths

/-! Reprice the budgets through actual binary operations and materialize the
same canonical fields as the edge and vertex covering entries. -/
namespace DirectedFlowCutGap.MeasuredBudgetPrices

open scoped BigOperators NNRat
open RawNonnegativeRational (Code)
open BinaryRational (Fraction StoredBounded)
open BinaryFractionalRows (stored_raw_bound)
open BinaryRationalNormalize (normalize)
open RationalEdgeThresholds (Weights cost)
open ConcurrentEdgeCoverWidths (MatrixFits)

variable {n r : ℕ}

def canonical (q : Code) : Fraction × ℕ :=
  let normalized := normalize q
  let packed := BinaryRawRational.encode normalized.1
  (packed.1,normalized.2+packed.2)

@[simp] theorem canonical_value (q : Code) :
    (canonical q).1 = (BinaryRawRational.encode (Code.ofNNRat q.value)).1 := by
  simp only [canonical,BinaryRationalNormalize.normalize_value]

def canonicalWork (B : ℕ) : ℕ := BinaryRationalNormalize.budget B+40*(B+2)^2

attribute [local irreducible] BinaryRationalNormalize.normalize BinaryRawRational.encode in
theorem canonical_bounds {q : Code} {B : ℕ} (fit : q.Bounded B) :
    StoredBounded (canonical q).1 (B+1) ∧ (canonical q).2 ≤ canonicalWork B := by
  have kept := BinaryRationalNormalize.normalize_width fit
  dsimp only [canonical,canonicalWork]
  exact ⟨BinaryRawRational.encode_width kept,
    Nat.add_le_add (BinaryRationalNormalize.normalize_paid fit) (BinaryRawRational.encode_paid kept)⟩

def tabulate {α : Type*} (f : Fin r → α × ℕ) : Vector α r × ℕ :=
  let reached := Vector.ofFn f
  (reached.map Prod.fst,∑ i : Fin r, (reached.get i).2)

@[simp] theorem tabulate_value {α : Type*} (f : Fin r → α × ℕ) (i : ℕ) (hi : i < r) :
    (tabulate f).1[i] = (f ⟨i,hi⟩).1 := by
  simp only [tabulate,Vector.getElem_map,Vector.getElem_ofFn]

theorem tabulate_charge {α : Type*} (f : Fin r → α × ℕ) {W : ℕ}
    (bound : ∀ i, (f i).2 ≤ W) : (tabulate f).2 ≤ r*W := by
  have each (i : Fin r) : ((Vector.ofFn f).get i).2 ≤ W := by
    change (Vector.ofFn f)[i.val].2 ≤ W
    simpa only [Vector.getElem_ofFn,Fin.eta] using bound i
  exact (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => each i)).trans_eq (by simp)

def cell (current : Fraction) (fee mass : Code) : Fraction × ℕ :=
  let input := BinaryRawRational.decode current
  let scaled := BinaryRawRational.div input.1 fee
  let reserve := BinaryRawRational.div Code.one mass
  let combined := BinaryRawRational.add scaled.1 reserve.1
  let packed := canonical combined.1
  (packed.1,input.2+scaled.2+reserve.2+combined.2+packed.2)

theorem cell_value (current : Fraction) (fee mass : Code) :
    (cell current fee mass).1 =
      (BinaryRawRational.encode (Code.ofNNRat ((BinaryRational.decode current).value/fee.value+1/mass.value))).1 := by
  simp only [cell,canonical_value,BinaryRawRational.decode_value,BinaryRawRational.div_value,
    BinaryRawRational.add_value,Code.value_div,Code.value_add,Code.value_one]

def cellWork (B F M : ℕ) : ℕ :=
  40*(B+1)^2+3*BinaryRawRational.budget (B+F+M)+canonicalWork (B+F+M+1)

attribute [local irreducible] BinaryRawRational.add BinaryRawRational.div in
theorem cell_bounds (current : Fraction) (fee mass : Code) {B F M : ℕ}
    (cap : StoredBounded current B) (feeFit : fee.Bounded F) (massFit : mass.Bounded M) :
    StoredBounded (cell current fee mass).1 (B+F+M+2) ∧ (cell current fee mass).2 ≤ cellWork B F M := by
  let input := BinaryRawRational.decode current
  let scaled := BinaryRawRational.div input.1 fee
  let reserve := BinaryRawRational.div Code.one mass
  let combined := BinaryRawRational.add scaled.1 reserve.1
  let W := B+F+M
  have inputFit : input.1.Bounded B := by
    rw [show input.1 = BinaryRational.decode current from BinaryRawRational.decode_value current]
    exact stored_raw_bound cap
  have scaledFit : scaled.1.Bounded (B+F) := by
    change (BinaryRawRational.div input.1 fee).1.Bounded (B+F)
    rw [BinaryRawRational.div_value]
    exact Code.bounded_div inputFit feeFit
  have reserveFit : reserve.1.Bounded M := by
    change (BinaryRawRational.div Code.one mass).1.Bounded M
    rw [BinaryRawRational.div_value]
    simpa only [Nat.zero_add] using Code.bounded_div Code.bounded_one massFit
  have combinedFit : combined.1.Bounded (W+1) := by
    change (BinaryRawRational.add scaled.1 reserve.1).1.Bounded (W+1)
    rw [BinaryRawRational.add_value]
    exact Code.bounded_add scaledFit reserveFit
  have inputWork := BinaryRawRational.decode_paid cap
  have scaledWork : scaled.2 ≤ BinaryRawRational.budget W :=
    BinaryRawRational.div_paid (Code.bounded_mono inputFit (by dsimp [W]; omega))
      (Code.bounded_mono feeFit (by dsimp [W]; omega))
  have reserveWork : reserve.2 ≤ BinaryRawRational.budget W :=
    BinaryRawRational.div_paid (Code.bounded_mono Code.bounded_one (Nat.zero_le _))
      (Code.bounded_mono massFit (by dsimp [W]; omega))
  have combinedWork : combined.2 ≤ BinaryRawRational.budget W :=
    BinaryRawRational.add_paid (Code.bounded_mono scaledFit (by dsimp [W]; omega))
      (Code.bounded_mono reserveFit (by dsimp [W]; omega))
  obtain ⟨fits,paid⟩ := canonical_bounds combinedFit
  refine ⟨fits,?_⟩
  change input.2+scaled.2+reserve.2+combined.2+(canonical combined.1).2 ≤ cellWork B F M
  change input.2 ≤ _ at inputWork
  change _ ≤ 40*(B+1)^2+3*BinaryRawRational.budget W+canonicalWork (W+1)
  omega

def vertex (prices : BinaryFractionalRows.Row n) (fee mass : Code) : BinaryFractionalRows.Row n × ℕ :=
  tabulate fun i => cell (prices.get i) fee mass

theorem vertex_value (prices : BinaryFractionalRows.Row n) (fee mass : Code) :
    (vertex prices fee mass).1 = ConcurrentVertexBudget.reprice prices fee.value mass.value := by
  apply Vector.ext
  intro i hi
  simp only [vertex,tabulate_value,cell_value,ConcurrentVertexBudget.reprice,
    ConcurrentVertexBudget.raw,Vector.getElem_ofFn]

theorem vertex_charge (prices : BinaryFractionalRows.Row n) (fee mass : Code) {B F M : ℕ}
    (fit : ∀ i, StoredBounded (prices.get i) B) (feeFit : fee.Bounded F) (massFit : mass.Bounded M) :
    (vertex prices fee mass).2 ≤ n*cellWork B F M :=
  tabulate_charge _ (fun i => (cell_bounds (prices.get i) fee mass (fit i) feeFit massFit).2)

def edge (prices : Weights n) (fee mass : Code) : Weights n × ℕ :=
  tabulate fun u => tabulate fun v => cell prices[u.val][v.val] fee mass

theorem edge_value (prices : Weights n) (fee mass : Code) :
    (edge prices fee mass).1 = ConcurrentEdgeMassBudget.reprice prices fee.value mass.value := by
  apply Vector.ext
  intro u hu
  apply Vector.ext
  intro v hv
  simp only [edge,tabulate_value,cell_value,ConcurrentEdgeMassBudget.reprice,
    ConcurrentEdgeZeroPrices.rawPrice,cost,BinaryFractionalWalkOracle.decodeCost,Vector.getElem_ofFn]

theorem edge_charge (prices : Weights n) (fee mass : Code) {B F M : ℕ}
    (fit : MatrixFits prices B) (feeFit : fee.Bounded F) (massFit : mass.Bounded M) :
    (edge prices fee mass).2 ≤ (n*n)*cellWork B F M := by
  rw [Nat.mul_assoc]
  exact tabulate_charge _ fun u =>
    tabulate_charge _ fun v => (cell_bounds prices[u.val][v.val] fee mass (fit u v) feeFit massFit).2

end DirectedFlowCutGap.MeasuredBudgetPrices
