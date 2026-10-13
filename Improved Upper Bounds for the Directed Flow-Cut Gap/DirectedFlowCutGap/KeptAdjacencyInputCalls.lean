import DirectedFlowCutGap.KeptAdjacencyInputCallLift

namespace DirectedFlowCutGap.KeptAdjacencyInput
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem mask_return {heap : NaturalHeap} {a b : ℕ} {s t : Bits} {vs : List Bits} {costs : List (Bits × Bits)}
    (hv : Vertices heap a vs) (hc : KeptMaskInput.Context heap b s t costs) (aligned : vs.length=costs.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 320)
    (stack : List (Frame ℕ 320)) (source : Bits) :
    ∃ ext root,ext.length=KeptMaskInput.cells s t vs costs ∧ NaturalRun program (KeptMaskInput.steps s t vs costs+2)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 198) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (KeptMaskInput.mask s t vs costs) := by
  obtain ⟨ext,root,len,core,rep⟩ := KeptMaskInput.scan hv hc aligned next c d hn [] source
  have lifted := child_return maskLabel KeptMaskInput.program mask_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,rep⟩
  simpa [KeptMaskInput.state,maskLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lifted

theorem matrix_return {heap : NaturalHeap} {a b : ℕ} {kept : Bits} {rows : List Bits}
    (ha : Matrix heap a rows) (hc : KeptAdjacencyMatrix.Context heap b kept kept)
    (aligned : rows.length=kept.length) (widths : ∀ u∈rows,u.length=kept.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 320)
    (stack : List (Frame ℕ 320)) (source : Bits) :
    ∃ ext root,ext.length=KeptAdjacencyMatrix.cells kept rows kept ∧ NaturalRun program (KeptAdjacencyMatrix.steps kept rows kept+2)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 282) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Matrix (heap++ext) root (KeptAdjacencyMatrix.matrix kept rows kept) := by
  obtain ⟨ext,root,len,core,rep⟩ := KeptAdjacencyMatrix.scan ha hc aligned widths next c d hn [] source
  have lifted := child_return matrixLabel KeptAdjacencyMatrix.program matrix_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,rep⟩
  simpa [KeptAdjacencyMatrix.state,matrixLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lifted
end DirectedFlowCutGap.KeptAdjacencyInput
