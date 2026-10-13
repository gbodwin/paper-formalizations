import DirectedFlowCutGap.ScalarAdditionRowTrace

namespace DirectedFlowCutGap.ScalarAdditionRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem row_high (scalar : Fraction) {xs : List Fraction} (initial : NaturalState 160)
    (pc0 : initial.pc=158) (hn : initial.next=initial.heap.length)
    (row : StoredList initial.heap initial.registers.a xs)
    (sc : Stored initial.heap initial.registers.b scalar) (empty : initial.stack=[]) :
    ∃ ext root,ext.length=cells scalar xs ∧
      NaturalRun program (1+steps scalar xs) initial []
        (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a
          initial.registers.b initial.registers.c root [] initial.source 159) ∧
      StoredList (initial.heap++ext) root (result scalar xs) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn row sc empty
      subst pc;subst stack
      have first : tickNatural program (state heap next a b c d [] source 158)=
          some ⟨state heap next a b c d [⟨159,.r3,⟨a,b,c,d⟩⟩] source 142,[],0⟩ := by
        simp [tickNatural,program,state]
      obtain ⟨ext,root,len,run,rep⟩ := row_return scalar row sc next c d hn ⟨a,b,c,d⟩ 159 [] source
      exact ⟨ext,root,len,by simpa [Nat.add_comm,state] using NaturalRun.step first run,rep⟩

def rowBits : List Fraction → ℕ
  | [] => 0
  | x::xs => x.num.length+x.den.length+rowBits xs

theorem member_bits {xs : List Fraction} {x : Fraction} (mem : x∈xs) :
    x.num.length+x.den.length ≤ rowBits xs := by
  induction xs with
  | nil => simp at mem
  | cons y ys ih =>
    simp only [List.mem_cons] at mem
    rcases mem with rfl|mem
    · simp only [rowBits];omega
    · have h := ih mem
      simp only [rowBits];omega

def instructionBound (n B : ℕ) : ℕ := n*(20000*(2*B+2)^2+11)+4

theorem steps_bound (scalar : Fraction) (xs : List Fraction) (B : ℕ)
    (sc : scalar.num.length+scalar.den.length ≤ B)
    (row : ∀ x∈xs,x.num.length+x.den.length ≤ B) :
    1+steps scalar xs ≤ instructionBound xs.length B := by
  induction xs with
  | nil => simp [steps,instructionBound]
  | cons x xs ih =>
    have hi := ih (fun z hz => row z (List.mem_cons_of_mem _ hz))
    have hx := row x List.mem_cons_self
    have size : CanonicalRationalAddition.inputSize x scalar ≤ 2*B+2 := by
      unfold CanonicalRationalAddition.inputSize
      omega
    have hp := (CanonicalRationalAddition.instructions_bound x scalar).trans
      (Nat.mul_le_mul_left 20000 (Nat.pow_le_pow_left size 2))
    simp only [steps,instructionBound,List.length_cons] at *
    nlinarith

def inputSteps (scalar : Fraction) (xs : List Fraction) : ℕ :=
  instructionBound xs.length (rowBits xs+scalar.num.length+scalar.den.length)

theorem steps_input_bound (scalar : Fraction) (xs : List Fraction) :
    1+steps scalar xs ≤ inputSteps scalar xs := by
  apply steps_bound scalar xs _ (by omega)
  intro x hx
  have h := member_bits hx
  omega

theorem result_length (scalar : Fraction) (xs : List Fraction) :
    (result scalar xs).length=xs.length := by simp [result]
end DirectedFlowCutGap.ScalarAdditionRow
