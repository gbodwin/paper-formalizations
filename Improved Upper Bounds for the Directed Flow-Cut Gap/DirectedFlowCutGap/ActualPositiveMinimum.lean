import DirectedFlowCutGap.PositiveMinimumExecution

namespace DirectedFlowCutGap.PositiveMinimum
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open BooleanTableRead PackedBooleanConstructor

theorem minimum_bit {H A : ℕ} {rows : List BinaryRational.Fraction} {words : List Bits} (aligned : words.length=rows.length)
    (W : ℕ) (size : ∀ q∈rows,q.num.length≤W ∧ q.den.length≤W)
    (initial : BitState 256) (bounded : initial.Bounded H A) (pc0 : initial.pc=254)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (verts : GraphDiscoveryProgram.Vertices (eraseState initial).heap (eraseState initial).registers.a words)
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.b (IndexedRationalRead.fields rows)) :
    ∃ k charge out,k≤ inputSteps rows W ∧ Run program k charge initial [] out ∧
      Result (eraseState out).heap (eraseState out).registers.d
        (select (PositiveInventory.selected (words.zip rows))) ∧
      GraphDiscoveryProgram.Vertices (eraseState out).heap (eraseState initial).registers.a words ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState initial).registers.b (IndexedRationalRead.fields rows) ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=255 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 256 H A
        (inputSteps rows W) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 254=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨k,ext,root,hk,high,rep⟩ := minimum rows words aligned verts table (eraseState initial).next
    (eraseState initial).registers.c (eraseState initial).registers.d
    dense' (eraseState initial).stack initial.source W size
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 255)=none := by simp [tickNatural,state,program]
  obtain ⟨charge,out,run,erase,_,_,sourceOut⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨k,charge,out,hk,run,?_,?_,?_,sourceOut,?_,?_,⟨ext,?_⟩,stop,?_⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact GraphDiscoveryProgram.vertices_extend verts ext
  · rw [erase];exact BinaryIndexedPairRead.table_extend table ext
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=255 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
  · exact (terminal_accounting run bounded stop).2.trans
      (SupportSearchEncoding.complete_mono 256 H A _ _ hk)

end DirectedFlowCutGap.PositiveMinimum
