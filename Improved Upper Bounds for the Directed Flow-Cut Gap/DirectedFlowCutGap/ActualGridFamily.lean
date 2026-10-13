import DirectedFlowCutGap.GridFamilyExecution
import DirectedFlowCutGap.GridFamilyOriginal

namespace DirectedFlowCutGap.GridFamily
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

theorem family_bit {n H B : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (exponent fuel : Bits)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    (initial : BitState 10180) (bounded : initial.Bounded H B) (pc0 : initial.pc=10178)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (context : Context (eraseState initial).heap (eraseState initial).registers.a adjacency costs xs)
    (exp : BoolList (eraseState initial).heap (eraseState initial).registers.b exponent)
    (input : BoolList (eraseState initial).heap (eraseState initial).registers.c fuel) :
    ∃ k charge out,Run program k charge initial [] out ∧
      StateList (eraseState out).heap (eraseState out).registers.d (values adjacency ds costs exponent fuel) ∧
      Context (eraseState out).heap (eraseState initial).registers.a adjacency costs xs ∧
      BoolList (eraseState out).heap (eraseState initial).registers.b exponent ∧
      BoolList (eraseState out).heap (eraseState initial).registers.c fuel ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=10179 ∧ value out.next=out.heap.length ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 10180 H B
        (instructionBound ds.length costs.toList exponent fuel+1) := by
  have nd : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have shape : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b
      (eraseState initial).registers.c (eraseState initial).registers.d [] initial.source 10178=eraseState initial := by
    cases initial with
    | mk heap next regs stack pc source =>
      cases regs
      simp_all [state,eraseState,State.map]
  obtain ⟨k,ext,root,bound,high,rep⟩ := compute adjacency costs encoded context exp input
    (eraseState initial).next (eraseState initial).registers.d nd initial.source
  rw [shape] at high
  have halt : tickNatural program
      (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
        (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
        root [] initial.source 10179)=none := by rfl
  obtain ⟨charge,out,run,erase,stop,cost,src⟩ := terminating_simulation bounded high halt
  refine ⟨k,charge,out,run,?_,?_,?_,?_,src,?_,?_,?_,⟨ext,congrArg State.heap erase⟩,stop,
    cost.trans (SupportSearchEncoding.complete_mono 10180 H B _ _ bound)⟩
  · rw [erase];exact rep
  · rw [erase];exact context_extend context ext
  · rw [erase];exact PackedBooleanConstructor.boolList_extend exp ext
  · rw [erase];exact PackedBooleanConstructor.boolList_extend input ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · exact congrArg State.pc erase
  · have h : (eraseState out).next=(eraseState out).heap.length := by rw [erase];simp [state,nd]
    simpa [eraseState,State.map] using h
end DirectedFlowCutGap.GridFamily
