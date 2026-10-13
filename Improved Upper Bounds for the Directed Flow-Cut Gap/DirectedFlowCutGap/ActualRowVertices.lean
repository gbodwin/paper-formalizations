import DirectedFlowCutGap.RowVerticesLabels

namespace DirectedFlowCutGap.RowVertices
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open CanonicalRationalSum (StoredList)
open GraphDiscoveryProgram (Vertices)

theorem enumerate_bit {H A : ℕ} {xs : List Fraction}
    (initial : BitState 44) (bounded : initial.Bounded H A) (pc0 : initial.pc=40)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : StoredList (eraseState initial).heap (eraseState initial).registers.a xs) :
    ∃ k charge out, Run program k charge initial [] out ∧
      Vertices (eraseState out).heap (eraseState out).registers.d (RowVertexScan.words xs.length []) ∧
      StoredList (eraseState out).heap (eraseState initial).registers.a xs ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=43 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 44 H A (instructionBound xs.length) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d [] initial.source 40=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨k,ext,scratch,root,high,rep,bound⟩ := enumerate input (eraseState initial).next
    (eraseState initial).registers.b (eraseState initial).registers.c (eraseState initial).registers.d dense' initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) scratch (eraseState initial).registers.b
      (eraseState initial).registers.c root [] initial.source 43)=none := by
    simp [tickNatural,state,program]
  obtain ⟨charge,out,run,erase,_,_,sourceOut⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨k,charge,out,run,?_,?_,sourceOut,?_,?_,⟨ext,?_⟩,stop,
    (terminal_accounting run bounded stop).2.trans
      (SupportSearchEncoding.complete_mono 44 H A _ _ bound)⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact CanonicalRationalSum.list_extend input ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=43 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
end DirectedFlowCutGap.RowVertices
