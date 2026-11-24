import DirectedFlowCutGap.MeasuredSparsityScore

/-! Calculate the exact cost and mass and retain the cheaper mode with the
same rule for ties as the existing sparsest-cut plan. -/
namespace DirectedFlowCutGap.MeasuredSparsitySelection

open scoped BigOperators NNRat
open RawNonnegativeRational (Code)
open FractionalCoverRawCore (RawRow RowBounded decodeRow rational)
open FractionalCover (objective value)
open MeasuredMultiplicityForms (dot dotWork)
open MeasuredSparsityScore (score scoreWidth)
open ChargedVertexModes (Mode)

variable {r : ℕ}

structure Totals where
  price : Code
  mass : Code
  charge : ℕ

def totals (c w : RawRow r) : Totals :=
  let price := dot c w
  let mass := dot (Vector.replicate r Code.one) w
  ⟨price.1,mass.1,price.2+mass.2⟩

theorem totals_price (c w : RawRow r) : rational (totals c w).price = objective (decodeRow c) (decodeRow w) := by
  simp only [totals,MeasuredMultiplicityForms.dot_value]

theorem totals_mass (c w : RawRow r) : rational (totals c w).mass = ∑ i, value (decodeRow w) i := by
  have one (i : Fin r) : value (decodeRow (Vector.replicate r Code.one)) i = 1 := by
    simp only [FractionalCoverRawCore.decode_value,FractionalCoverRawCore.get,Vector.getElem_replicate,
      FractionalCoverRawCore.rational_one]
  simp only [totals,MeasuredMultiplicityForms.dot_value,objective,one,one_mul]

theorem totals_bounds (c w : RawRow r) {B W : ℕ} (price : RowBounded c B) (row : RowBounded w W) :
    let t := totals c w
    t.price.Bounded (r*(B+W+1)) ∧ t.mass.Bounded (r*(W+1)) ∧ t.charge ≤ dotWork r B W+dotWork r 0 W := by
  have ones : RowBounded (Vector.replicate r Code.one) 0 := by
    intro i
    simpa only [FractionalCoverRawCore.get,Vector.getElem_replicate] using Code.bounded_one
  obtain ⟨feeFields,feeWork⟩ := MeasuredMultiplicityForms.dot_bounds c w price row
  obtain ⟨massFields,massWork⟩ := MeasuredMultiplicityForms.dot_bounds (Vector.replicate r Code.one) w ones row
  refine ⟨feeFields,?_,Nat.add_le_add feeWork massWork⟩
  simpa only [totals,Nat.zero_add] using massFields

structure Scored where
  mode : Mode
  receipt : Code

def modes (n m : ℕ) (cost mass h : Code) : Scored × ℕ :=
  let size := score n m cost mass h .size
  let volume := score n m cost mass h .mass
  let cmp := BinaryRawRational.le volume.1 size.1
  let best := if cmp.1 then (⟨.mass,volume.1⟩ : Scored) else ⟨.size,size.1⟩
  (best,size.2+volume.2+cmp.2)

def uncode (result : Scored) : Mode × ℚ≥0 := (result.mode,result.receipt.value)

theorem modes_value (n m : ℕ) (cost mass h : Code) (wh : h.value = NormalizedOptimalMode.harmonic m) :
    let s := ConcurrentEdgeBudgetSelection.score n m cost.value mass.value .size
    let t := ConcurrentEdgeBudgetSelection.score n m cost.value mass.value .mass
    uncode (modes n m cost mass h).1 = if t ≤ s then (.mass,t) else (.size,s) := by
  let size := score n m cost mass h .size
  let volume := score n m cost mass h .mass
  let s := ConcurrentEdgeBudgetSelection.score n m cost.value mass.value .size
  let t := ConcurrentEdgeBudgetSelection.score n m cost.value mass.value .mass
  have hv : (BinaryRawRational.le volume.1 size.1).1 = true ↔ t ≤ s := by
    rw [BinaryRawRational.le_value,Code.le_eq_true,
      MeasuredSparsityScore.score_value n m cost mass h .mass wh,
      MeasuredSparsityScore.score_value n m cost mass h .size wh]
  change uncode (modes n m cost mass h).1 = if t ≤ s then (.mass,t) else (.size,s)
  by_cases won : t ≤ s
  · dsimp only [modes]
    rw [ite_eq_left won,ite_eq_left (hv.mpr won)]
    simp only [uncode,MeasuredSparsityScore.score_value n m cost mass h .mass wh,t]
  · dsimp only [modes]
    rw [ite_eq_right won,ite_eq_right (fun b => won (hv.mp b))]
    simp only [uncode,MeasuredSparsityScore.score_value n m cost mass h .size wh,s]

attribute [local irreducible] BinaryRawRational.le in
theorem modes_bounds (n m : ℕ) (price mass h : Code) {B M H : ℕ}
    (p : price.Bounded B) (v : mass.Bounded M) (w : h.Bounded H) :
    let width := scoreWidth n m B M H
    (modes n m price mass h).1.receipt.Bounded width ∧
      (modes n m price mass h).2 ≤ 43*BinaryRawRational.budget width := by
  let size := score n m price mass h .size
  let volume := score n m price mass h .mass
  obtain ⟨sFit,sPaid⟩ := MeasuredSparsityScore.score_bounds n m price mass h .size p v w
  obtain ⟨tFit,tPaid⟩ := MeasuredSparsityScore.score_bounds n m price mass h .mass p v w
  have cmpPaid := BinaryRawRational.le_paid tFit sFit
  dsimp only [modes]
  refine ⟨?_,?_⟩
  · split
    · exact tFit
    · exact sFit
  · change size.2+volume.2+(BinaryRawRational.le volume.1 size.1).2 ≤ _
    exact (Nat.add_le_add (Nat.add_le_add sPaid tPaid) cmpPaid).trans_eq (by omega)

end DirectedFlowCutGap.MeasuredSparsitySelection
