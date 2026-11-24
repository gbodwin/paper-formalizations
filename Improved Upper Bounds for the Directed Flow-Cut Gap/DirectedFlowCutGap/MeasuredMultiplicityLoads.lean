import DirectedFlowCutGap.MeasuredMultiplicityForms

/-! Binary arithmetic for the initial weights and the accumulated flow
and per-resource loads of a multiplicity cover. -/
namespace DirectedFlowCutGap.MeasuredMultiplicityLoads

open scoped BigOperators
open RawNonnegativeRational (Code)
open FractionalCover (value value_ofFn delta initial)
open FractionalCoverRawCore (RawRow get rational decodeRow RowBounded)
open MultiplicityCover (Choice coeff amount deposit)
open MultiplicityCoverWidths (ColumnFits)
open MeasuredMultiplicityUpdate (ofNat_fits amountPaid amount_value)

variable {r : ℕ}

def deltaPaid (r : ℕ) : Code × ℕ :=
  let a := Code.ofNat r
  let square := BinaryRawRational.mul a a
  let denom := BinaryRawRational.mul (Code.ofNat 3) square.1
  let result := BinaryRawRational.div (Code.ofNat 2) denom.1
  (result.1,square.2+denom.2+result.2)

theorem delta_value (r : ℕ) : rational (deltaPaid r).1 = delta r := by
  simp only [deltaPaid,delta,pow_two,BinaryRawRational.mul_value,BinaryRawRational.div_value,
    FractionalCoverRawCore.rational_mul,FractionalCoverRawCore.rational_div,
    FractionalCoverRawCore.rational_nat,Nat.cast_ofNat]

attribute [local irreducible] BinaryRawRational.mul BinaryRawRational.div in
private theorem delta_bounds (r : ℕ) :
    (deltaPaid r).1.Bounded (2*r+3) ∧ (deltaPaid r).2 ≤ 3*BinaryRawRational.budget (2*r+3) := by
  let w := 2*r+3
  let square := BinaryRawRational.mul (Code.ofNat r) (Code.ofNat r)
  let denom := BinaryRawRational.mul (Code.ofNat 3) square.1
  let q := BinaryRawRational.div (Code.ofNat 2) denom.1
  have dim : (Code.ofNat r).Bounded r := ofNat_fits Nat.lt_two_pow_self.le
  have two : (Code.ofNat 2).Bounded 1 := ofNat_fits (by decide)
  have three : (Code.ofNat 3).Bounded 2 := ofNat_fits (by decide)
  have sqFit : square.1.Bounded (r+r) := by
    change (BinaryRawRational.mul (Code.ofNat r) (Code.ofNat r)).1.Bounded (r+r)
    rw [BinaryRawRational.mul_value]
    exact Code.bounded_mul dim dim
  have denFit : denom.1.Bounded (2+(r+r)) := by
    change (BinaryRawRational.mul (Code.ofNat 3) square.1).1.Bounded (2+(r+r))
    rw [BinaryRawRational.mul_value]
    exact Code.bounded_mul three sqFit
  have sqPaid : square.2 ≤ BinaryRawRational.budget w :=
    BinaryRawRational.mul_paid (Code.bounded_mono dim (by dsimp [w];omega))
      (Code.bounded_mono dim (by dsimp [w];omega))
  have denPaid : denom.2 ≤ BinaryRawRational.budget w :=
    BinaryRawRational.mul_paid (Code.bounded_mono three (by dsimp [w];omega))
      (Code.bounded_mono sqFit (by dsimp [w];omega))
  have resultPaid : q.2 ≤ BinaryRawRational.budget w :=
    BinaryRawRational.div_paid (Code.bounded_mono two (by dsimp [w];omega))
      (Code.bounded_mono denFit (by dsimp [w];omega))
  change q.1.Bounded w ∧ square.2+denom.2+q.2 ≤ 3*BinaryRawRational.budget w
  refine ⟨?_,by omega⟩
  change (BinaryRawRational.div (Code.ofNat 2) denom.1).1.Bounded w
  rw [BinaryRawRational.div_value]
  exact Code.bounded_mono (Code.bounded_div two denFit) (by dsimp [w]; omega)

def start (c : RawRow r) : RawRow r × ℕ :=
  let small := deltaPaid r
  let items := Vector.ofFn fun i => BinaryRawRational.div small.1 (get c i)
  (items.map Prod.fst,small.2+∑ i : Fin r,(items.get i).2)

theorem start_value (c : RawRow r) : decodeRow (start c).1 = initial (decodeRow c) := by
  apply Vector.ext
  intro i hi
  simp only [decodeRow,start,initial,FractionalCoverRawCore.get,Vector.getElem_ofFn,Vector.getElem_map,
    BinaryRawRational.div_value,FractionalCoverRawCore.rational_div,delta_value,value_ofFn]

theorem start_bounds (c : RawRow r) {B : ℕ} (price : RowBounded c B) :
    RowBounded (start c).1 (B+2*r+3) ∧
      (start c).2 ≤ (r+3)*BinaryRawRational.budget (B+2*r+3) := by
  let small := deltaPaid r
  let limit := B+2*r+3
  obtain ⟨fit,spent⟩ := delta_bounds r
  have costs (i : Fin r) : (BinaryRawRational.div small.1 (get c i)).2 ≤ BinaryRawRational.budget limit :=
    BinaryRawRational.div_paid (Code.bounded_mono fit (by dsimp [limit];omega))
      (Code.bounded_mono (price i) (by dsimp [limit];omega))
  have prev : small.2 ≤ 3*BinaryRawRational.budget limit := by
    refine spent.trans ?_
    have ordered : 2*r+3 ≤ limit := by dsimp [limit]; omega
    unfold BinaryRawRational.budget
    exact Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left 8192 (Nat.pow_le_pow_left (Nat.add_le_add_right ordered 3) 2))
  constructor
  · intro i
    simp only [start,FractionalCoverRawCore.get,Vector.getElem_map,Vector.getElem_ofFn,BinaryRawRational.div_value]
    exact Code.bounded_mono (Code.bounded_div fit (price i)) (by omega)
  · have each (i : Fin r) :
      ((Vector.ofFn fun j => BinaryRawRational.div small.1 (get c j)).get i).2 ≤ BinaryRawRational.budget limit := by
      change (Vector.ofFn fun j => BinaryRawRational.div small.1 (get c j))[i.val].2 ≤ _
      simpa only [Vector.getElem_ofFn,Fin.eta] using costs i
    have rest := (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => each i)).trans_eq
      (by simp : (∑ _i : Fin r,BinaryRawRational.budget limit) = r*BinaryRawRational.budget limit)
    change small.2+(∑ i : Fin r,((Vector.ofFn fun j => BinaryRawRational.div small.1 (get c j)).get i).2) ≤ _
    exact (Nat.add_le_add prev rest).trans_eq (by unfold limit; ring)

def loadCell (value shared : Code) (count : ℕ) : Code × ℕ :=
  let amount := BinaryRawRational.mul shared (Code.ofNat count)
  let larger := BinaryRawRational.add value amount.1
  (larger.1,amount.2+larger.2)

theorem loadCell_value (value shared : Code) (count : ℕ) :
    rational (loadCell value shared count).1 = rational value+rational shared*(count : ℚ) := by
  simp only [loadCell,BinaryRawRational.mul_value,BinaryRawRational.add_value,
    FractionalCoverRawCore.rational_mul,FractionalCoverRawCore.rational_add,FractionalCoverRawCore.rational_nat]

structure Added (r : ℕ) where
  total : Code
  loads : RawRow r
  charge : ℕ

def add (c : RawRow r) (pick : Choice r) (oldTotal : Code) (loads : RawRow r) : Added r :=
  let shared := amountPaid c pick
  let total := BinaryRawRational.add oldTotal shared.1
  let rows := Vector.ofFn fun i => loadCell (get loads i) shared.1 (coeff pick.column i)
  ⟨total.1,rows.map Prod.fst,shared.2+total.2+∑ i : Fin r,(rows.get i).2⟩

theorem add_total (c : RawRow r) (pick : Choice r) (oldTotal : Code) (loads : RawRow r) :
    rational (add c pick oldTotal loads).total = rational oldTotal+amount (decodeRow c) pick := by
  simp only [add,BinaryRawRational.add_value,FractionalCoverRawCore.rational_add,amount_value]

theorem add_loads (c : RawRow r) (pick : Choice r) (oldTotal : Code) (loads : RawRow r) :
    decodeRow (add c pick oldTotal loads).loads = Vector.ofFn fun i =>
      value (decodeRow loads) i+deposit (decodeRow c) pick i := by
  apply Vector.ext
  intro i hi
  simp only [decodeRow,add,FractionalCoverRawCore.get,Vector.getElem_ofFn,Vector.getElem_map,
    loadCell_value,amount_value,deposit,value_ofFn]

def loadWork (r B U L : ℕ) : ℕ := (2+r*2)*BinaryRawRational.budget (max L (B+2*U))

theorem add_bounds (c : RawRow r) (pick : Choice r) (oldTotal : Code) (loads : RawRow r)
    {B U L : ℕ} (price : RowBounded c B) (counts : ColumnFits pick.column U)
    (total : oldTotal.Bounded L) (row : RowBounded loads L) :
    let z := add c pick oldTotal loads
    z.total.Bounded (L+(B+2*U)+1) ∧ RowBounded z.loads (L+(B+2*U)+1) ∧ z.charge ≤ loadWork r B U L := by
  let Q := max L (B+2*U)
  let shared := amountPaid c pick
  let newTotal := BinaryRawRational.add oldTotal shared.1
  have piv := ofNat_fits (counts pick.pivot)
  have sharedFit : shared.1.Bounded (B+U) := by
    change (BinaryRawRational.div _ _).1.Bounded _
    rw [BinaryRawRational.div_value]
    exact Code.bounded_div (price pick.pivot) piv
  have upper : B+2*U ≤ Q := le_max_right _ _
  have prior : L ≤ Q := le_max_left _ _
  have sharedFee : shared.2 ≤ BinaryRawRational.budget Q :=
    BinaryRawRational.div_paid (Code.bounded_mono (price pick.pivot) (by omega))
      (Code.bounded_mono piv (by omega))
  have totalFee : newTotal.2 ≤ BinaryRawRational.budget Q :=
    BinaryRawRational.add_paid (Code.bounded_mono total prior) (Code.bounded_mono sharedFit (by omega))
  have each (i : Fin r) :
      (loadCell (get loads i) shared.1 (coeff pick.column i)).1.Bounded (L+(B+2*U)+1) ∧
      (loadCell (get loads i) shared.1 (coeff pick.column i)).2 ≤ 2*BinaryRawRational.budget Q := by
    let count := Code.ofNat (coeff pick.column i)
    have fits := ofNat_fits (counts i)
    have raw : (BinaryRawRational.mul shared.1 count).1.Bounded (B+2*U) := by
      rw [BinaryRawRational.mul_value]
      exact Code.bounded_mono (Code.bounded_mul sharedFit fits) (by omega)
    have a : (BinaryRawRational.mul shared.1 count).2 ≤ BinaryRawRational.budget Q :=
      BinaryRawRational.mul_paid (Code.bounded_mono sharedFit (by omega)) (Code.bounded_mono fits (by omega))
    have b : (BinaryRawRational.add (get loads i) (BinaryRawRational.mul shared.1 count).1).2 ≤
        BinaryRawRational.budget Q :=
      BinaryRawRational.add_paid (Code.bounded_mono (row i) prior) (Code.bounded_mono raw upper)
    change (BinaryRawRational.add (get loads i) (BinaryRawRational.mul shared.1 count).1).1.Bounded _ ∧ _ ≤ _
    refine ⟨?_,Nat.add_le_add a b |>.trans_eq (by omega)⟩
    rw [BinaryRawRational.add_value]
    exact Code.bounded_add (row i) raw
  refine ⟨?_,?_,?_⟩
  · change newTotal.1.Bounded _
    change (BinaryRawRational.add _ _).1.Bounded _
    rw [BinaryRawRational.add_value]
    exact Code.bounded_mono (Code.bounded_add total sharedFit) (by omega)
  · intro i
    simpa only [add,FractionalCoverRawCore.get,Vector.getElem_map,Vector.getElem_ofFn,shared] using (each i).1
  · have cell (i : Fin r) : ((Vector.ofFn fun j => loadCell (get loads j) shared.1 (coeff pick.column j)).get i).2
        ≤ 2*BinaryRawRational.budget Q := by
      change (Vector.ofFn fun j => loadCell (get loads j) shared.1 (coeff pick.column j))[i.val].2 ≤ _
      simpa only [Vector.getElem_ofFn,Fin.eta] using (each i).2
    have subtotal := (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => cell i)).trans_eq
      (by simp : (∑ _i : Fin r,2*BinaryRawRational.budget Q) = r*(2*BinaryRawRational.budget Q))
    exact (Nat.add_le_add (Nat.add_le_add sharedFee totalFee) subtotal).trans_eq (by unfold Q loadWork; ring)

end DirectedFlowCutGap.MeasuredMultiplicityLoads
