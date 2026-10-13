import DirectedFlowCutGap.PackingLoadRowBounds
import DirectedFlowCutGap.ScalarQuotientRowRefinement

namespace DirectedFlowCutGap.PackingLoadRow
open BinaryRational

theorem result_ofFn (amount : Fraction) {n : ℕ} (y : Fin n → Fraction) (mask : Fin n → Bool) :
    result amount (List.ofFn y) (List.ofFn mask)=
      List.ofFn (fun i => PackingLoadEntry.result (mask i) amount (y i)) := by
  induction n with
  | zero => simp [result]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_succ]
    simp only [result]
    rw [ih]

theorem result_eq_addLoads {m : ℕ} (loads : BinaryFractionalRows.Row m)
    (mask : Vector Bool m) (amount : Fraction) :
    result amount loads.toList mask.toList=(BinaryFractionalRows.addLoads loads mask amount).1.toList := by
  have hm : mask.toList=List.ofFn (fun i : Fin m => mask[i.val]) := by
    rw [←Vector.toList_ofFn]
    congr
    ext i hi
    simp
  rw [ScalarQuotientRow.row_toList,hm,result_ofFn]
  simp [BinaryFractionalRows.addLoads,EncodedRoundingInput.tabulate_value,Vector.toList_ofFn,
    PackingLoadEntry.result,PackingLoadEntry.operand]
end DirectedFlowCutGap.PackingLoadRow
