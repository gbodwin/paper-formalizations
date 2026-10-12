import DirectedFlowCutGap.ScalarQuotientRowTrace

namespace DirectedFlowCutGap.ScalarQuotientRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem row_high (mode : Bool) (scalar : Fraction) {xs : List Fraction} (initial : NaturalState 182)
    (pc0 : initial.pc=180) (hn : initial.next=initial.heap.length)
    (row : StoredList initial.heap initial.registers.a xs)
    (sc : Stored initial.heap initial.registers.b scalar) (empty : initial.stack=[]) :
    ∃ ext root,ext.length=cells mode scalar xs ∧
      NaturalRun (program mode) (1+steps mode scalar xs) initial []
        (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a
          initial.registers.b initial.registers.c root [] initial.source 181) ∧
      StoredList (initial.heap++ext) root (result mode scalar xs) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn row sc empty
      subst pc;subst stack
      have first : tickNatural (program mode) (state heap next a b c d [] source 180)=
          some ⟨state heap next a b c d [⟨181,.r3,⟨a,b,c,d⟩⟩] source 164,[],0⟩ := by
        simp [tickNatural,program,state]
      obtain ⟨ext,root,len,run,rep⟩ := row_return mode scalar row sc next c d hn ⟨a,b,c,d⟩ 181 [] source
      exact ⟨ext,root,len,by simpa [Nat.add_comm,state] using NaturalRun.step first run,rep⟩

def instructionBound (n B : ℕ) : ℕ := n*(600*(4*B+2)^2+14)+4

theorem steps_bound (mode : Bool) (scalar : Fraction) (xs : List Fraction) (B : ℕ)
    (sc : StoredBounded scalar B) (row : ∀ x∈xs,StoredBounded x B) :
    1+steps mode scalar xs ≤ instructionBound xs.length B := by
  induction xs with
  | nil => simp [steps,instructionBound]
  | cons x xs ih =>
    have hi := ih (fun z hz => row z (List.mem_cons_of_mem _ hz))
    have hx := row x List.mem_cons_self
    have nn : StoredBounded (numerator mode scalar x) B := by cases mode <;> simp [numerator,sc,hx]
    have dd : StoredBounded (denominator mode scalar x) B := by cases mode <;> simp [denominator,sc,hx]
    have size : CanonicalRationalQuotient.inputSize (numerator mode scalar x) (denominator mode scalar x) ≤ 4*B+2 := by
      unfold CanonicalRationalQuotient.inputSize
      obtain ⟨a,b⟩ := nn;obtain ⟨c,d⟩ := dd;omega
    have hp := (CanonicalRationalQuotient.steps_bound (numerator mode scalar x) (denominator mode scalar x)).trans
      (Nat.mul_le_mul_left 600 (Nat.pow_le_pow_left size 2))
    simp only [steps,instructionBound,List.length_cons] at *
    split <;> nlinarith

theorem result_length (mode : Bool) (scalar : Fraction) (xs : List Fraction) :
    (result mode scalar xs).length=xs.length := by simp [result]

theorem result_width (mode : Bool) (scalar : Fraction) (xs : List Fraction) (B : ℕ)
    (sc : StoredBounded scalar B) (row : ∀ x∈xs,StoredBounded x B) :
    ∀ z∈result mode scalar xs,StoredBounded z (B+B+1) := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
  have hb := row x hx
  have nn : StoredBounded (numerator mode scalar x) B := by cases mode <;> simp [numerator,sc,hb]
  have dd : StoredBounded (denominator mode scalar x) B := by cases mode <;> simp [denominator,sc,hb]
  exact BinaryRational.div_stored_bounded (BinaryFractionalRows.stored_raw_bound nn)
    (BinaryFractionalRows.stored_raw_bound dd)
end DirectedFlowCutGap.ScalarQuotientRow
