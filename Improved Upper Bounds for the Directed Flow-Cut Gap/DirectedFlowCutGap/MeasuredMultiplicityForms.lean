import DirectedFlowCutGap.MeasuredMultiplicityUpdate

/-! Binary rational dot products and normalization for covering columns.
Actual primitive charges include conversion to and from canonical
binary fields. -/
namespace DirectedFlowCutGap.MeasuredMultiplicityForms

open scoped BigOperators
open RawNonnegativeRational (Code)
open FractionalCover (objective value value_ofFn)
open FractionalCoverRawCore (RawRow get rational decodeRow RowBounded sumCodes)
open MultiplicityCover (Column coeff length normalized)
open MultiplicityCoverWidths (ColumnFits)
open MeasuredMultiplicityUpdate (ofNat_fits)

variable {r : ℕ}

def sum : List Code → Code × ℕ
  | [] => (Code.zero,0)
  | q::qs =>
    let t := sum qs
    let combined := BinaryRawRational.add q t.1
    (combined.1,t.2+combined.2)

theorem sum_value (items : List Code) : (sum items).1 = sumCodes items := by
  induction items with
  | nil => rfl
  | cons q qs ih => simp only [sum,sumCodes,BinaryRawRational.add_value,ih]

theorem sum_charge (items : List Code) {B K : ℕ} (fit : ∀ q ∈ items, q.Bounded B)
    (enough : items.length ≤ K) : (sum items).2 ≤ items.length*BinaryRawRational.budget (K*(B+1)) := by
  induction items with
  | nil => simp [sum]
  | cons q qs ih =>
    let b := BinaryRawRational.budget (K*(B+1))
    have qFit := fit q List.mem_cons_self
    have qsFit (c : Code) (present : c ∈ qs) := fit c (List.mem_cons_of_mem _ present)
    have rest := ih qsFit ((Nat.le_succ _).trans enough)
    have stored : (sum qs).1.Bounded (qs.length*(B+1)) := by
      rw [sum_value]
      exact FractionalCoverRawCore.sumCodes_bounded qs B qsFit
    have low : B ≤ K*(B+1) := by
      have one : 1 ≤ K := (Nat.succ_pos qs.length).trans_le enough
      exact (Nat.le_succ _).trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (B+1) one)
    have charges : (BinaryRawRational.add q (sum qs).1).2 ≤ b :=
      BinaryRawRational.add_paid (Code.bounded_mono qFit low)
        (Code.bounded_mono stored (Nat.mul_le_mul_right _ ((Nat.le_succ _).trans enough)))
    change (sum qs).2 + (BinaryRawRational.add q (sum qs).1).2 ≤ _
    rw [List.length_cons,Nat.add_mul,Nat.one_mul]
    exact Nat.add_le_add rest charges

private def products (c y : RawRow r) : List (Code × ℕ) :=
  List.ofFn fun i => BinaryRawRational.mul (get c i) (get y i)

def dot (c y : RawRow r) : Code × ℕ :=
  let cells := products c y
  let z := sum (cells.map Prod.fst)
  (z.1,(cells.map Prod.snd).sum+z.2)

theorem dot_value (c y : RawRow r) : rational (dot c y).1 = objective (decodeRow c) (decodeRow y) := by
  unfold dot
  dsimp only
  rw [sum_value]
  simp only [products,List.map_ofFn,Function.comp_def,BinaryRawRational.mul_value,
    FractionalCoverRawCore.rational_sum,FractionalCoverRawCore.rational_mul,List.sum_ofFn,
    objective,FractionalCoverRawCore.decode_value]

private theorem sum_work_le_length (c y : RawRow r) {B W : ℕ} (price : RowBounded c B)
    (weights : RowBounded y W) :
    ((products c y).map Prod.snd).sum ≤ r*BinaryRawRational.budget (B+W) := by
  simp only [products,List.map_ofFn,Function.comp_def,List.sum_ofFn]
  have each (i : Fin r) : (BinaryRawRational.mul (get c i) (get y i)).2 ≤ BinaryRawRational.budget (B+W) :=
    BinaryRawRational.mul_paid (Code.bounded_mono (price i) (Nat.le_add_right ..))
      (Code.bounded_mono (weights i) (Nat.le_add_left ..))
  exact (Finset.sum_le_sum (fun i _ => each i)).trans_eq (by simp)

def dotWork (r B W : ℕ) : ℕ :=
  r*BinaryRawRational.budget (B+W) + r*BinaryRawRational.budget (r*(B+W+1))

theorem dot_bounds (c y : RawRow r) {B W : ℕ} (price : RowBounded c B) (weights : RowBounded y W) :
    (dot c y).1.Bounded (r*(B+W+1)) ∧ (dot c y).2 ≤ dotWork r B W := by
  let items := (products c y).map Prod.fst
  have size : items.length = r := by simp [items,products]
  have fit (q : Code) (present : q ∈ items) : q.Bounded (B+W) := by
    simp only [items,products,List.map_ofFn,Function.comp_def,List.mem_ofFn,BinaryRawRational.mul_value] at present
    obtain ⟨i,rfl⟩ := present
    exact Code.bounded_mul (price i) (weights i)
  have fields := FractionalCoverRawCore.sumCodes_bounded items (B+W) fit
  have charged := sum_charge items fit size.le
  rw [size] at fields charged
  exact ⟨by simpa only [dot,← sum_value,items] using fields,
    Nat.add_le_add (sum_work_le_length c y price weights) charged⟩

def counts (p : Column r) : RawRow r := Vector.ofFn fun i => Code.ofNat (coeff p i)

theorem counts_fit (p : Column r) {U : ℕ} (fit : ColumnFits p U) : RowBounded (counts p) U := by
  intro i
  rw [counts,FractionalCoverRawCore.get_ofFn]
  exact ofNat_fits (fit i)

def lengthPaid (y : RawRow r) (p : Column r) : Code × ℕ := dot (counts p) y

theorem length_value (y : RawRow r) (p : Column r) :
    rational (lengthPaid y p).1 = length (decodeRow y) p := by
  simp only [lengthPaid,dot_value,objective,length,FractionalCoverRawCore.decode_value,
    counts,FractionalCoverRawCore.get_ofFn,FractionalCoverRawCore.rational_nat]

def normalize (y : RawRow r) (p : Column r) : RawRow r × ℕ :=
  let scale := lengthPaid y p
  let quotients := Vector.ofFn fun i => BinaryRawRational.div (get y i) scale.1
  (quotients.map Prod.fst,scale.2+∑ i : Fin r,(quotients.get i).2)

theorem normalize_value (y : RawRow r) (p : Column r) :
    decodeRow (normalize y p).1 = normalized (decodeRow y) p := by
  apply Vector.ext
  intro i hi
  simp only [decodeRow,normalize,normalized,Vector.getElem_ofFn,Vector.getElem_map,
    FractionalCoverRawCore.get,BinaryRawRational.div_value,FractionalCoverRawCore.rational_div,
    length_value,value_ofFn]

def normalizeWork (r U W : ℕ) : ℕ :=
  dotWork r U W + r*BinaryRawRational.budget (max W (r*(U+W+1)))

theorem normalize_bounds (y : RawRow r) (p : Column r) {U W : ℕ}
    (weights : RowBounded y W) (coefficients : ColumnFits p U) :
    RowBounded (normalize y p).1 (W+r*(U+W+1)) ∧
      (normalize y p).2 ≤ normalizeWork r U W := by
  let scale := lengthPaid y p
  obtain ⟨size,charge⟩ := dot_bounds (counts p) y (counts_fit p coefficients) weights
  have fit : scale.1.Bounded (r*(U+W+1)) := size
  let Q := max W (r*(U+W+1))
  have each (i : Fin r) : (BinaryRawRational.div (get y i) scale.1).2 ≤ BinaryRawRational.budget Q :=
    BinaryRawRational.div_paid (Code.bounded_mono (weights i) (le_max_left ..))
      (Code.bounded_mono fit (le_max_right ..))
  constructor
  · intro i
    simp only [FractionalCoverRawCore.get,normalize,Vector.getElem_map,Vector.getElem_ofFn,
      BinaryRawRational.div_value]
    exact Code.bounded_div (weights i) fit
  · have work (i : Fin r) :
        ((Vector.ofFn fun v => BinaryRawRational.div (get y v) scale.1).get i).2 ≤
          BinaryRawRational.budget Q := by
      change (Vector.ofFn fun v => BinaryRawRational.div (get y v) scale.1)[i.val].2 ≤ _
      simpa only [Vector.getElem_ofFn,Fin.eta] using each i
    have total := (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => work i)).trans_eq
      (by simp : (∑ _i : Fin r,BinaryRawRational.budget Q) = r*BinaryRawRational.budget Q)
    exact Nat.add_le_add charge total

end DirectedFlowCutGap.MeasuredMultiplicityForms
