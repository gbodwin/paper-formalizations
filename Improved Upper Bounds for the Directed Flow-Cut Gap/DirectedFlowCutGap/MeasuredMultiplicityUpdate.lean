import DirectedFlowCutGap.MultiplicityCoverWidths
import DirectedFlowCutGap.FractionalCoverRawEncoding
import DirectedFlowCutGap.BinaryRawRational

/-! Execute the multiplicity weight update with binary rational primitives.
The charge covers those primitive operations and their conversions. -/
namespace DirectedFlowCutGap.MeasuredMultiplicityUpdate

open scoped BigOperators
open RawNonnegativeRational (Code)
open FractionalCover (value value_ofFn)
open FractionalCoverRawCore (RawRow get rational decodeRow RowBounded)
open MultiplicityCover (Choice coeff amount deposit update)

variable {r : ℕ}

def amountPaid (c : RawRow r) (pick : Choice r) : Code × ℕ :=
  BinaryRawRational.div (get c pick.pivot) (Code.ofNat (coeff pick.column pick.pivot))

theorem amount_value (c : RawRow r) (pick : Choice r) :
    rational (amountPaid c pick).1 = amount (decodeRow c) pick := by
  simp only [amountPaid,amount,BinaryRawRational.div_value,FractionalCoverRawCore.rational_div,
    FractionalCoverRawCore.rational_nat,FractionalCoverRawCore.decode_value]

def updateCell (price old shared : Code) (multiplicity : ℕ) : Code × ℕ :=
  let put := BinaryRawRational.mul shared (Code.ofNat multiplicity)
  let twice := BinaryRawRational.mul (Code.ofNat 2) price
  let ratio := BinaryRawRational.div put.1 twice.1
  let factor := BinaryRawRational.add Code.one ratio.1
  let result := BinaryRawRational.mul old factor.1
  (result.1,put.2+twice.2+ratio.2+factor.2+result.2)

theorem cell_value (price old shared : Code) (multiplicity : ℕ) :
    rational (updateCell price old shared multiplicity).1 =
      rational old*(1+rational shared*(multiplicity : ℚ)/(2*rational price)) := by
  simp only [updateCell,BinaryRawRational.mul_value,BinaryRawRational.div_value,BinaryRawRational.add_value,
    FractionalCoverRawCore.rational_mul,FractionalCoverRawCore.rational_div,FractionalCoverRawCore.rational_add,
    FractionalCoverRawCore.rational_one,FractionalCoverRawCore.rational_nat,Nat.cast_ofNat]

private def cells (c y : RawRow r) (pick : Choice r) (shared : Code) : Vector (Code × ℕ) r :=
  Vector.ofFn fun i => updateCell (get c i) (get y i) shared (coeff pick.column i)

def run (c y : RawRow r) (pick : Choice r) : RawRow r × ℕ :=
  let shared := amountPaid c pick
  let reached := cells c y pick shared.1
  (reached.map Prod.fst,shared.2+∑ i : Fin r, (reached.get i).2)

theorem run_value (c y : RawRow r) (pick : Choice r) :
    decodeRow (run c y pick).1 = update (decodeRow c) (decodeRow y) pick := by
  apply Vector.ext
  intro i hi
  simp only [decodeRow,run,cells,update,Vector.getElem_ofFn,Vector.getElem_map,
    FractionalCoverRawCore.get,cell_value,amount_value,deposit,value_ofFn]

theorem ofNat_fits {x U : ℕ} (fit : x ≤ 2^U) : (Code.ofNat x).Bounded U :=
  ⟨fit,Nat.one_le_pow _ _ (by decide)⟩

def operandWidth (B U W : ℕ) : ℕ := max W (2*B+2*U+2)

theorem cell_bounds (price old shared : Code) (multiplicity : ℕ) {B U W : ℕ}
    (cp : price.Bounded B) (weights : old.Bounded W) (amount : shared.Bounded (B+U))
    (count : multiplicity ≤ 2^U) :
    (updateCell price old shared multiplicity).1.Bounded (W+(2*B+2*U+2)) ∧
      (updateCell price old shared multiplicity).2 ≤ 5*BinaryRawRational.budget (operandWidth B U W) := by
  let limit := operandWidth B U W
  let put := BinaryRawRational.mul shared (Code.ofNat multiplicity)
  let twice := BinaryRawRational.mul (Code.ofNat 2) price
  let ratio := BinaryRawRational.div put.1 twice.1
  let factor := BinaryRawRational.add Code.one ratio.1
  let result := BinaryRawRational.mul old factor.1
  have occ := ofNat_fits count
  have two : (Code.ofNat 2).Bounded 1 := ofNat_fits (by decide)
  have putFit : put.1.Bounded (B+2*U) := by
    change (BinaryRawRational.mul shared (Code.ofNat multiplicity)).1.Bounded _
    rw [BinaryRawRational.mul_value]
    exact Code.bounded_mono (Code.bounded_mul amount occ) (by omega)
  have twiceFit : twice.1.Bounded (1+B) := by
    change (BinaryRawRational.mul _ _).1.Bounded _
    rw [BinaryRawRational.mul_value]
    exact Code.bounded_mul two cp
  have ratioFit : ratio.1.Bounded (2*B+2*U+1) := by
    change (BinaryRawRational.div _ _).1.Bounded _
    rw [BinaryRawRational.div_value]
    exact Code.bounded_mono (Code.bounded_div putFit twiceFit) (by omega)
  have factorFit : factor.1.Bounded (2*B+2*U+2) := by
    change (BinaryRawRational.add _ _).1.Bounded _
    rw [BinaryRawRational.add_value]
    exact Code.bounded_mono (Code.bounded_add Code.bounded_one ratioFit) (by omega)
  have bigEnough : 2*B+2*U+2 ≤ limit := le_max_right _ _
  have Wfit : W ≤ limit := le_max_left _ _
  have workPut : put.2 ≤ BinaryRawRational.budget limit :=
    BinaryRawRational.mul_paid (Code.bounded_mono amount (by omega)) (Code.bounded_mono occ (by omega))
  have workTwice : twice.2 ≤ BinaryRawRational.budget limit :=
    BinaryRawRational.mul_paid (Code.bounded_mono two (by omega)) (Code.bounded_mono cp (by omega))
  have workRatio : ratio.2 ≤ BinaryRawRational.budget limit :=
    BinaryRawRational.div_paid (Code.bounded_mono putFit (by omega)) (Code.bounded_mono twiceFit (by omega))
  have workFactor : factor.2 ≤ BinaryRawRational.budget limit :=
    BinaryRawRational.add_paid (Code.bounded_mono Code.bounded_one zero_le) (Code.bounded_mono ratioFit (by omega))
  have workResult : result.2 ≤ BinaryRawRational.budget limit :=
    BinaryRawRational.mul_paid (Code.bounded_mono weights Wfit) (Code.bounded_mono factorFit bigEnough)
  change result.1.Bounded _ ∧ put.2+twice.2+ratio.2+factor.2+result.2 ≤ 5*BinaryRawRational.budget limit
  refine ⟨?_,by omega⟩
  change (BinaryRawRational.mul _ _).1.Bounded _
  rw [BinaryRawRational.mul_value]
  exact Code.bounded_mul weights factorFit

theorem run_bounds (c y : RawRow r) (pick : Choice r) {B U W : ℕ}
    (price : RowBounded c B) (weights : RowBounded y W)
    (counts : MultiplicityCoverWidths.ColumnFits pick.column U) :
    RowBounded (run c y pick).1 (W+(2*B+2*U+2)) ∧
      (run c y pick).2 ≤ (1+r*5)*BinaryRawRational.budget (operandWidth B U W) := by
  let shared := amountPaid c pick
  let limit := operandWidth B U W
  have coeffFit := ofNat_fits (counts pick.pivot)
  have sharedFit : shared.1.Bounded (B+U) := by
    change (BinaryRawRational.div _ _).1.Bounded _
    rw [BinaryRawRational.div_value]
    exact Code.bounded_div (price pick.pivot) coeffFit
  have right : 2*B+2*U+2 ≤ limit := le_max_right _ _
  have charge : shared.2 ≤ BinaryRawRational.budget limit :=
    BinaryRawRational.div_paid (Code.bounded_mono (price pick.pivot) (by omega))
      (Code.bounded_mono coeffFit (by omega))
  have each (i : Fin r) := cell_bounds (get c i) (get y i) shared.1 (coeff pick.column i)
    (price i) (weights i) sharedFit (counts i)
  constructor
  · intro i
    simpa only [run,cells,FractionalCoverRawCore.get,Vector.getElem_map,Vector.getElem_ofFn,shared] using (each i).1
  · have cellsBound (i : Fin r) : ((cells c y pick shared.1).get i).2 ≤ 5*BinaryRawRational.budget limit := by
      change ((cells c y pick shared.1)[i.val]).2 ≤ _
      simpa only [cells,Vector.getElem_ofFn,Fin.eta] using (each i).2
    have all :
        (∑ i : Fin r, ((cells c y pick shared.1).get i).2) ≤ r*(5*BinaryRawRational.budget limit) := by
      exact (Finset.sum_le_sum (fun i _ => cellsBound i)).trans_eq (by simp)
    change shared.2+(∑ i : Fin r, ((cells c y pick shared.1).get i).2) ≤ _
    exact (Nat.add_le_add charge all).trans_eq (by unfold limit; ring)

end DirectedFlowCutGap.MeasuredMultiplicityUpdate
