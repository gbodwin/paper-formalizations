import DirectedFlowCutGap.CapacityBottleneckBounds

/-! Physical stable bottleneck selection consumes actual mask flags and original
capacity records. It preserves the actual vertex payload and pays one halt. -/
namespace DirectedFlowCutGap.CapacityBottleneck
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

theorem graph_bit {n H A : ℕ} (label : Fin n → Bits) (capacity : Row n) (mask : Vector Bool n)
    (initial : BitState 244) (bounded : initial.Bounded H A) (pc0 : initial.pc=240)
    (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (flags : BoolList (eraseState initial).heap (eraseState initial).registers.a
      ((List.finRange n).map fun i => mask[i.val]))
    (context : GraphContext (eraseState initial).heap (eraseState initial).registers.b label capacity)
    (W : ℕ) (widths : ∀ i,(get capacity i).num.length≤W ∧ (get capacity i).den.length≤W) :
    ∃ xs charge out,List.Forall₂ (EncodesSlot label capacity mask) xs (List.finRange n) ∧
      Run program (selectedSteps (value initial.next) xs) charge initial [] out ∧
      Output (eraseState out).heap (eraseState out).registers.d label capacity
        (BinaryFractionalGraphOracle.bottleneck capacity mask).1 ∧
      out.source=initial.source ∧ out.stack=[] ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧
        ext.length=selectedCells (value initial.next) xs) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations≤completeBound 244 H A (instructionBound n W) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨xs,final,encoded,high,rep,source,stack,ext,halt⟩ :=
    graph_high label capacity mask (eraseState initial) pc0 hn' empty' flags context
  obtain ⟨charge,out,run,erase,_,_,src⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have ht : tickNatural program final=none := by simp [tickNatural,halt]
    rw [ht] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  have len : xs.length=n := by simpa using encoded.length_eq
  have bound := selected_steps_le xs (value initial.next) W (encoded_widths encoded widths)
  rw [len] at bound
  refine ⟨xs,charge,out,encoded,run,?_,src.trans source,?_,?_,stop,
    (terminal_accounting run bounded stop).2.trans (SupportSearchEncoding.complete_mono 244 H A _ _ bound)⟩
  · rw [erase];exact rep
  · have h : (eraseState out).stack=[] := by rw [erase];exact stack
    simpa [eraseState,State.map] using h
  · rw [erase];exact ext

end DirectedFlowCutGap.CapacityBottleneck
