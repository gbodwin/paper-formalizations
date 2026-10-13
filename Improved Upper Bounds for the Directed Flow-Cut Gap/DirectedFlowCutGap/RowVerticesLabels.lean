import DirectedFlowCutGap.RowVerticesExecution

namespace DirectedFlowCutGap.RowVertices
open BinaryArithmetic

theorem words_values (n : ℕ) (acc : Bits) :
    (RowVertexScan.words n acc).map value=List.range' (value acc) n := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    simp only [RowVertexScan.words,List.map_cons,List.range'_succ,ih]
    rw [(increment_spec true acc).1]
    rfl

theorem words_width (n : ℕ) (acc : Bits) (w : Bits) (mem : w∈RowVertexScan.words n acc) :
    w.length≤acc.length+n := by
  induction n generalizing acc with
  | zero => simp [RowVertexScan.words] at mem
  | succ n ih =>
    simp only [RowVertexScan.words,List.mem_cons] at mem
    rcases mem with rfl | mem
    · omega
    · have h := ih (increment true acc).1 mem
      have hi := (increment_spec true acc).2.1
      omega

def vertexLabel {n : ℕ} (i : Fin n) : Bits :=
  (RowVertexScan.words n [])[i.val]'(by rw [RowVertexScan.words_length];exact i.isLt)

theorem label_numeric {n : ℕ} (i : Fin n) : value (vertexLabel i)=i.val := by
  have h := words_values n []
  have hx := congrArg (fun xs : List ℕ => xs[i.val]?) h
  simpa [vertexLabel,List.getElem?_eq_getElem,i.isLt,RowVertexScan.words_length,value] using hx

theorem label_width {n : ℕ} (i : Fin n) : (vertexLabel i).length≤n := by
  have h := words_width n [] (vertexLabel i) (List.getElem_mem _)
  simpa using h

theorem labels_exact (n : ℕ) : (List.finRange n).map vertexLabel=RowVertexScan.words n [] := by
  apply List.ext_getElem
  · simp [RowVertexScan.words_length]
  · intro i hi hj
    simp [vertexLabel]
end DirectedFlowCutGap.RowVertices
