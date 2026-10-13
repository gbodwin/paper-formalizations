import DirectedFlowCutGap.KeptAdjacencyInputTrace

namespace DirectedFlowCutGap.KeptAdjacencyInput
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

def inputSteps (s t : Bits) (vs : List Bits) (costs : List (Bits × Bits)) (rows : List Bits) : ℕ :=
  KeptMaskInput.inputSteps s t vs costs+KeptAdjacencyMatrix.inputSteps rows+11

theorem steps_bound (s t : Bits) (vs : List Bits) (costs : List (Bits × Bits)) (rows : List Bits) :
    steps s t vs costs rows+1 ≤ inputSteps s t vs costs rows := by
  have hk := KeptMaskInput.steps_bound s t vs costs
  have hm := KeptAdjacencyMatrix.steps_bound (kept s t vs costs) rows (kept s t vs costs)
  unfold steps inputSteps
  omega

theorem scan {heap : NaturalHeap} {a b : ℕ} {s t : Bits} {vs : List Bits}
    {costs : List (Bits × Bits)} {rows : List Bits}
    (hv : Vertices heap a vs) (hc : Context heap b s t costs rows)
    (aligned : vs.length=costs.length) (height : rows.length=vs.length)
    (widths : ∀ u∈rows,u.length=vs.length)
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 320)) (source : Bits) :
    ∃ ext root,ext.length=cells s t vs costs rows ∧ NaturalRun program (steps s t vs costs rows+1)
      (state heap next a b c d stack source 318) []
      (state (heap++ext) (next+ext.length) a b c root stack source 319) ∧
      Matrix (heap++ext) root (result s t vs costs rows) := by
  obtain ⟨ext,root,len,run,rep⟩ := input_return hv hc aligned height widths next c d hn ⟨a,b,c,d⟩ 319 stack source
  have call : tickNatural program (state heap next a b c d stack source 318)=
      some ⟨state heap next a b c d (⟨319,.r3,⟨a,b,c,d⟩⟩::stack) source 290,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step call run,rep⟩

theorem kept_original {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (s t : Fin n) (c : BinaryFractionalRows.Row n) :
    kept (label s) (label t) (List.ofFn label) (IndexedRationalRead.fields c.toList)=
      KeptAdjacencyMatrix.keptFlags (BinaryFractionalDispatch.zeroMask c).1 s t := by
  have h := KeptMaskInput.mask_original label hlabel s t (List.ofFn (fun i : Fin n => i)) c
  simp only [List.map_ofFn,Function.comp_def] at h
  change KeptMaskInput.mask _ _ _ _=_
  rw [h]
  apply List.ext_getElem
  · simp [KeptAdjacencyMatrix.keptFlags]
  · intro i hi hj
    simp [KeptAdjacencyMatrix.keptFlags]

theorem result_original {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (s t : Fin n) (c : BinaryFractionalRows.Row n) (adjacency : BinaryFractionalWalkOracle.Adjacency n) :
    result (label s) (label t) (List.ofFn label) (IndexedRationalRead.fields c.toList)
      (GraphRelaxationRefinement.matrix adjacency)=
      GraphRelaxationRefinement.matrix
        (BinaryFractionalDispatch.keptAdjacency adjacency (BinaryFractionalDispatch.zeroMask c).1 s t).1 := by
  unfold result
  rw [kept_original label hlabel,KeptAdjacencyMatrix.matrix_original]
end DirectedFlowCutGap.KeptAdjacencyInput
