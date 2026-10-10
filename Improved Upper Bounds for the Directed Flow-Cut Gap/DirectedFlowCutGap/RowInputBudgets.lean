import DirectedFlowCutGap.BinaryInputBudgets
import DirectedFlowCutGap.BinaryFractionalRows

/-! Obtain actual graph-size and stored-width words from the supplied stored
rational row. Both numerator and denominator padding are scanned. The field
view includes an explicit list/record allowance; physical heap addressing and
raw denominator validation remain their separate existing interfaces. -/
namespace DirectedFlowCutGap.RowInputBudgets
open BinaryArithmetic BinaryRational BinaryFractionalRows BinaryInputBudgets

def fields {n : ℕ} (w : Row n) : List (Bits × Bits) :=
  w.toList.map (fun a => (a.num,a.den))

def prepare {n : ℕ} (w : Row n) : Words :=
  let s := scan (fields w)
  {s with operations := s.operations+8*w.toList.length+1}

theorem fields_length {n : ℕ} (w : Row n) : (fields w).length=n := by
  simp [fields]

theorem fields_contain {n : ℕ} (w : Row n) (i : Fin n) :
    ((get w i).num,(get w i).den)∈fields w := by
  apply List.mem_map.mpr
  refine ⟨get w i,?_,rfl⟩
  exact Vector.mem_toList_iff.mpr (Vector.getElem_mem i.isLt)

/-- The very same scanned width bounds all stored fields, with no externally
supplied resource/count word or stored-width certificate. -/
theorem prepare_spec {n : ℕ} (w : Row n) :
    value (prepare w).resources=n ∧
    value (prepare w).width=storedSize (fields w) ∧
    (∀ i,StoredBounded (get w i) (value (prepare w).width)) ∧
    (prepare w).resources.length ≤ inputSize (fields w) ∧
    (prepare w).width.length ≤ 2*inputSize (fields w) ∧
    (prepare w).operations ≤ 144*(inputSize (fields w)+1)^2 := by
  obtain ⟨hn,hw,hr,hb,hc⟩ := scan_spec (fields w)
  have hsize := sizes (fields w)
  rw [fields_length] at hn hsize
  refine ⟨hn,hw,?_,hr,hb,?_⟩
  · intro i
    change StoredBounded (get w i) (value (scan (fields w)).width)
    rw [hw]
    exact fields_bounded (fields_contain w i)
  · change (scan (fields w)).operations+8*w.toList.length+1 ≤ _
    rw [Vector.length_toList]
    nlinarith

end DirectedFlowCutGap.RowInputBudgets
