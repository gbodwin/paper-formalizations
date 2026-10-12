import DirectedFlowCutGap.PackingGuardBounds

namespace DirectedFlowCutGap.PackingGuard
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

/-- Recomputes the old step guard even for a previously stopped state. The
actual current weights and original capacity spine are the only arithmetic
inputs; the objective and one record are constructed in this same run. -/
theorem guard_bit {n H A : ℕ} (capacity : Row n) (s : BinaryFractionalCore.State n)
    (label : Fin n → Bits) (initial : BitState 484)
    (bounded : initial.Bounded H A) (pc0 : initial.pc=470)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (row : StoredList (eraseState initial).heap (eraseState initial).registers.a capacity.toList)
    (rep : PackingStart.StateRecord (eraseState initial).heap (eraseState initial).registers.b label s)
    (B : ℕ) (hc : ∀ x∈capacity.toList,StoredBounded x B)
    (hy : ∀ x∈s.weights.toList,StoredBounded x B) :
    ∃ charge out,Run program (steps capacity.toList s.weights.toList) charge initial [] out ∧
      (eraseState out).heap[(eraseState out).registers.d]?=
        some (.flag (BinaryRational.le one (objective capacity s.weights).1).1) ∧
      PackingStart.StateRecord (eraseState out).heap (eraseState initial).registers.b label s ∧
      StoredList (eraseState out).heap (eraseState initial).registers.a capacity.toList ∧
      Context (eraseState out).heap (eraseState out).registers.c
        (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=480 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧
        ext.length=cells capacity.toList s.weights.toList) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 484 H A (instructionBound n B) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b
      (eraseState initial).registers.c (eraseState initial).registers.d [] initial.source 470=
      eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,oneRoot,objectiveRoot,flagRoot,len,high,flag,context,retained,_⟩ :=
    state_guard capacity s label row rep (eraseState initial).next
      (eraseState initial).registers.c (eraseState initial).registers.d dense' initial.source
  rw [start] at high
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have halt : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have hh : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          oneRoot objectiveRoot ((eraseState initial).next+1) flagRoot [] initial.source 480)=none := rfl
    rw [hh] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  have cost := (terminal_accounting run bounded halt).2
  have hb := steps_bound capacity.toList s.weights.toList B (by simp) hc hy
  simp only [Vector.length_toList] at hb
  have hm : completeBound 484 H A (steps capacity.toList s.weights.toList) ≤
      completeBound 484 H A (instructionBound n B) := by
    unfold completeBound runBound stepBound
    gcongr
  refine ⟨charge,out,run,?_,?_,?_,?_,source,?_,?_,⟨ext,?_,len⟩,halt,cost.trans hm⟩
  · rw [erase];exact flag
  · rw [erase];exact retained
  · rw [erase];exact list_extend row ext
  · rw [erase];exact context
  · have hs : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using hs
  · have hp : (eraseState out).pc=480 := by rw [erase];rfl
    exact hp
  · rw [erase];rfl
end DirectedFlowCutGap.PackingGuard
