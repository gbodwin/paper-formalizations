import DirectedFlowCutGap.EdgeRoundStorage
import DirectedFlowCutGap.RunnerCutoffStorage

/-! Insert the reached vertex cutoff storage after the edge gadget's arrays
and before the cut projection, including when packed execution exhausts tape. -/
namespace DirectedFlowCutGap.EdgePackedRoundLayout

open BinaryArithmetic Polynomial EncodedArrayStorage EncodedEdgeLineInput
open BinaryArrayNestedStorage (Code gridSchedule)
open FractionalCoverRawCore (RawRow)
open PhysicalIntegerRoundingCost (eval_mono)

def Model {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ)
    (row : RawRow (lineSize n)) (tape : Bits) (code : Code) : Prop :=
  let input := (BinaryEdgeProjection.roundingInputWithControl D row).1.1
  let g := (BinaryEdgeGadget.buildWithControl input).1.1
  let draw := PaidVertexRounding.runner mode T g.data tape
  let output := if draw.1.isSome then EdgeRoundStorage.projectionCode n g.size else []
  ∃ cutoff : Code, RunnerCutoffStorage.Model mode T g.data tape cutoff ∧
    code=gridSchedule n n++EdgeGadgetArrayStorage.codeFor n g.size++cutoff++output

set_option maxHeartbeats 1000000 in
theorem arrays : ∃ cells copies : Polynomial ℕ, ∀ {n : ℕ} (D : Input n)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (row : RawRow (lineSize n)) (tape : Bits),
    ∃ code : Code, Model D mode T row tape code ∧ fresh code ≤ cells.eval (n+T) ∧
      code.length ≤ copies.eval (n+T) := by
  obtain ⟨oldCells,oldCopies,oldBound⟩ := EdgeRoundStorage.polynomial
  obtain ⟨cutoffCells,cutoffCopies,cutoffBound⟩ := RunnerCutoffStorage.arrays
  let dimension := BinaryEdgeGadget.dimension (X : Polynomial ℕ)
  let pad := dimension+X
  refine ⟨oldCells+cutoffCells.comp pad,oldCopies+cutoffCopies.comp pad,?_⟩
  intro n D mode T row tape
  let input := (BinaryEdgeProjection.roundingInputWithControl D row).1.1
  let g := (BinaryEdgeGadget.buildWithControl input).1.1
  let draw := PaidVertexRounding.runner mode T g.data tape
  let output := if draw.1.isSome then EdgeRoundStorage.projectionCode n g.size else []
  let before := gridSchedule n n++EdgeGadgetArrayStorage.codeFor n g.size
  let x := n+T
  have nBound : n ≤ x := Nat.le_add_right _ _
  have dim : g.size ≤ dimension.eval x := by
    have same : g=(BinaryEdgeGadget.build input).1 := congrArg Prod.fst (BinaryEdgeGadget.build_control_projection input)
    rw [same]
    apply (BinaryEdgeGadget.size_le input).trans
    simp only [dimension,BinaryEdgeGadget.dimension,eval_mul,eval_add,eval_ofNat,eval_X]
    gcongr
  have wide : g.size+T ≤ pad.eval x := by
    simp only [pad,eval_add,eval_X]
    exact Nat.add_le_add dim (Nat.le_add_left _ _)
  obtain ⟨cutoff,modeled,used,events⟩ := cutoffBound mode T g.data tape
  have previous : fresh (before++output) ≤ oldCells.eval n ∧ (before++output).length ≤ oldCopies.eval n :=
    oldBound D mode T row tape
  let code := before++cutoff++output
  refine ⟨code,⟨cutoff,modeled,rfl⟩,?_,?_⟩
  · have rest := previous.1.trans (eval_mono oldCells nBound)
    have pack := used.trans (eval_mono cutoffCells wide)
    change fresh code ≤ (oldCells+cutoffCells.comp pad).eval x
    simp only [code,fresh_append,eval_add,eval_comp] at rest ⊢
    omega
  · have rest := previous.2.trans (eval_mono oldCopies nBound)
    have pack := events.trans (eval_mono cutoffCopies wide)
    change code.length ≤ (oldCopies+cutoffCopies.comp pad).eval x
    simp only [code,List.length_append,eval_add,eval_comp] at rest ⊢
    omega

end DirectedFlowCutGap.EdgePackedRoundLayout
