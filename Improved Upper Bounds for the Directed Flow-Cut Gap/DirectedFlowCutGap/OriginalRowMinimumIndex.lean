import DirectedFlowCutGap.ActualOriginalRowMinimum

namespace DirectedFlowCutGap.OriginalRowMinimum
open BinaryArithmetic BinaryRational

theorem selected_index {n : ℕ} (costs : BinaryFractionalRows.Row n) {word : Bits} {q : Fraction}
    (selected : result costs.toList=some (word,q)) :
    ∃ i : Fin n,(BinaryFractionalDispatch.minimumPositive costs).1=some i ∧
      word=RowVertices.vertexLabel i ∧ q=BinaryFractionalRows.get costs i := by
  rw [result_original] at selected
  cases hm : (BinaryFractionalDispatch.minimumPositive costs).1 with
  | none => simp [hm] at selected
  | some i =>
    simp only [hm,Option.map_some,Option.some.injEq,Prod.mk.injEq] at selected
    exact ⟨i,rfl,selected.1.symm,selected.2.symm⟩

theorem selected_valid {n : ℕ} (costs : BinaryFractionalRows.Row n) {word : Bits} {q : Fraction}
    (selected : result costs.toList=some (word,q)) : value word<n ∧ word.length≤n := by
  obtain ⟨i,_,rfl,_⟩ := selected_index costs selected
  exact ⟨by rw [RowVertices.label_numeric];exact i.isLt,RowVertices.label_width i⟩
end DirectedFlowCutGap.OriginalRowMinimum
