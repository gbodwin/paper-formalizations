import DirectedFlowCutGap.PackingUpdateRowBounds
import DirectedFlowCutGap.ScalarQuotientRowRefinement

namespace DirectedFlowCutGap.PackingUpdateRow
open BinaryRational

theorem result_ofFn (amount : Fraction) {n : ℕ} (c y : Fin n → Fraction) (mask : Fin n → Bool) :
    result amount (List.ofFn c) (List.ofFn y) (List.ofFn mask)=
      List.ofFn (fun i => if mask i then PackingEntry.result (c i) amount (y i) else y i) := by
  induction n with
  | zero => simp [result]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_succ,List.ofFn_succ]
    simp only [result]
    rw [ih]

theorem result_eq_update {m : ℕ} (c y : BinaryFractionalRows.Row m)
    (mask : Vector Bool m) (j : Fin m) :
    result (BinaryFractionalRows.get c j) c.toList y.toList mask.toList=
      (BinaryFractionalRows.update c y mask j).1.toList := by
  have hm : mask.toList=List.ofFn (fun i : Fin m => mask[i.val]) := by
    rw [←Vector.toList_ofFn]
    congr
    ext i hi
    simp
  rw [ScalarQuotientRow.row_toList,ScalarQuotientRow.row_toList,hm,result_ofFn]
  simp [BinaryFractionalRows.update,EncodedRoundingInput.tabulate_value,Vector.toList_ofFn,
    BinaryFractionalRows.factor,PackingEntry.result,PackingEntry.factor,PackingEntry.quotient,
    PackingEntry.doubled]
  funext i
  cases mask[i.val] <;> simp
end DirectedFlowCutGap.PackingUpdateRow
