import DirectedFlowCutGap.PackingAmountExecution

namespace DirectedFlowCutGap.PackingAmount
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def instructionBound (m D : ℕ) : ℕ := 6*m+10*D+16

theorem steps_bound {m : ℕ} (q : BinaryFractionalCore.Choice m)
    (labels : Fin m → Bits) (numeric : ∀ j,value (labels j)=j.val)
    (D : ℕ) (width : ∀ j,(labels j).length≤D) :
    BinaryIndexedPairRead.steps (labels q.bottleneck)+6≤ instructionBound m D := by
  have h := BinaryIndexedPairRead.steps_bound (labels q.bottleneck)
  rw [numeric] at h
  have hi := q.bottleneck.isLt
  have hw := width q.bottleneck
  unfold instructionBound
  omega

/-- The selected Choice record supplies the actual binary index to a real
capacity-list read. Its padded fields are retained by the allocated amount. -/
theorem choice_bit {m H A : ℕ} (capacity : Row m) (q : BinaryFractionalCore.Choice m)
    (labels : Fin m → Bits) (numeric : ∀ j,value (labels j)=j.val)
    (initial : BitState 44) (bounded : initial.Bounded H A)
    (pc0 : initial.pc=40) (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (choice : OracleChoice.StoredChoice (eraseState initial).heap (eraseState initial).registers.a labels q)
    (table : StoredList (eraseState initial).heap (eraseState initial).registers.b capacity.toList)
    (D : ℕ) (width : ∀ j,(labels j).length≤D) :
    ∃ charge out index,
      Run program (BinaryIndexedPairRead.steps (labels q.bottleneck)+6) charge initial [] out ∧
      Stored (eraseState out).heap (eraseState out).registers.d (get capacity q.bottleneck) ∧
      BoolList (eraseState out).heap index (labels q.bottleneck) ∧
      StoredList (eraseState out).heap (eraseState initial).registers.b capacity.toList ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=42 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=q.bottleneck.val+2) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations≤completeBound 44 H A (instructionBound m D) := by
  have dense : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have frames : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,root,index,len,high,rep,word⟩ :=
    choice_high capacity q labels numeric (eraseState initial) pc0 dense frames choice table
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have halt : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have ht : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          index (eraseState initial).registers.b (eraseState initial).registers.c root []
          (eraseState initial).source 42)=none := rfl
    rw [ht] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  have cost := (terminal_accounting run bounded halt).2
  have hb := steps_bound q labels numeric D width
  have hm : completeBound 44 H A (BinaryIndexedPairRead.steps (labels q.bottleneck)+6)≤
      completeBound 44 H A (instructionBound m D) := by
    unfold completeBound runBound stepBound
    gcongr
  refine ⟨charge,out,index,run,?_,?_,?_,source,?_,?_,⟨ext,?_,len⟩,halt,cost.trans hm⟩
  · rw [erase];exact rep
  · rw [erase];exact word
  · rw [erase];exact list_extend table ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=42 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
end DirectedFlowCutGap.PackingAmount
