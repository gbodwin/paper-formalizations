import DirectedFlowCutGap.ActualPositiveInventory
import DirectedFlowCutGap.ScalarQuotientRowRefinement
import DirectedFlowCutGap.BinaryFractionalDispatch

namespace DirectedFlowCutGap.PositiveInventory
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal

theorem selected_indices {n : ℕ} (c : BinaryFractionalRows.Row n) (label : Fin n → Bits)
    (is : List (Fin n)) :
    selected (is.map fun i => (label i,BinaryFractionalRows.get c i))=
      (BinaryFractionalDispatch.positiveIndices c is).1.map
        (fun i => (label i,BinaryFractionalRows.get c i)) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    cases hz : (BinaryArithmetic.isZero (BinaryFractionalRows.get c i).num).1 <;>
      simp [selected,BinaryFractionalDispatch.positiveIndices,BinaryFractionalGraphOracle.read_value,
        BinaryRational.isZero,hz,selected] at ih ⊢ <;> exact ih

theorem selected_original {n : ℕ} (c : BinaryFractionalRows.Row n) (label : Fin n → Bits) :
    selected (((List.finRange n).map label).zip c.toList)=
      (BinaryFractionalDispatch.positiveIndices c (List.finRange n)).1.map
        (fun i => (label i,BinaryFractionalRows.get c i)) := by
  rw [ScalarQuotientRow.row_toList,List.ofFn_eq_map,List.zip_map']
  exact selected_indices c label _
end DirectedFlowCutGap.PositiveInventory
