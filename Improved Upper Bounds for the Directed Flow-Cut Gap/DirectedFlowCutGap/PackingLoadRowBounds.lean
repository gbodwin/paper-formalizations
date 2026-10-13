import DirectedFlowCutGap.PackingLoadRowTrace

namespace DirectedFlowCutGap.PackingLoadRow
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem row_high (amount : Fraction) {ys : List Fraction} {mask : List Bool}
    (initial : NaturalState 200) (pc0 : initial.pc=190) (hn : initial.next=initial.heap.length)
    (loads : StoredList initial.heap initial.registers.a ys)
    {mr ar : ℕ} (flags : BoolList initial.heap mr mask) (amt : Stored initial.heap ar amount)
    (context : initial.heap[initial.registers.b]?=some (.pair mr ar))
    (aligned : ys.length=mask.length) (empty : initial.stack=[]) :
    ∃ ext root,ext.length=cells amount ys mask ∧
      NaturalRun program (1+steps amount ys mask) initial []
        (state (initial.heap++ext) (initial.next+ext.length) root initial.registers.b
          initial.registers.c initial.registers.d [] initial.source 191) ∧
      StoredList (initial.heap++ext) root (result amount ys mask) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn loads flags amt context empty
      subst pc;subst stack
      have first : tickNatural program (state heap next a b c d [] source 190)=
          some ⟨state heap next a b c d [⟨191,.r0,⟨a,b,c,d⟩⟩] source 160,[],0⟩ := by
        simp [tickNatural,program,state]
      obtain ⟨ext,root,len,run,rep⟩ := row_return amount loads flags amt context aligned
        next c d hn ⟨a,b,c,d⟩ 191 [] source
      exact ⟨ext,root,len,by simpa [Nat.add_comm,state] using NaturalRun.step first run,rep⟩

def entryBound (B : ℕ) : ℕ := 20000*(4*(B+1)+2)^2+8

def instructionBound (n B : ℕ) : ℕ := n*(entryBound B+21)+4

theorem operand_width (enabled : Bool) (amount : Fraction) (B : ℕ) (ha : StoredBounded amount B) :
    StoredBounded (PackingLoadEntry.operand enabled amount) (B+1) := by
  cases enabled with
  | false => simp [PackingLoadEntry.operand,StoredBounded,zero]
  | true => exact ⟨ha.1.trans (by omega),ha.2.trans (by omega)⟩

theorem entry_steps_bound (enabled : Bool) (amount y : Fraction) (B : ℕ)
    (ha : StoredBounded amount B) (hy : StoredBounded y B) :
    PackingLoadEntry.steps enabled amount y ≤ entryBound B := by
  have ho := operand_width enabled amount B ha
  have hs : CanonicalRationalAddition.inputSize y (PackingLoadEntry.operand enabled amount)≤4*(B+1)+2 := by
    have a:=hy.1;have b:=hy.2;have c:=ho.1;have d:=ho.2
    unfold CanonicalRationalAddition.inputSize
    omega
  have hb := (CanonicalRationalAddition.instructions_bound y (PackingLoadEntry.operand enabled amount)).trans
    (Nat.mul_le_mul_left 20000 (Nat.pow_le_pow_left hs 2))
  unfold PackingLoadEntry.steps entryBound
  split <;> omega

theorem steps_bound (amount : Fraction) (ys : List Fraction) (mask : List Bool) (B : ℕ)
    (amt : StoredBounded amount B) (loads : ∀ x∈ys,StoredBounded x B) :
    1+steps amount ys mask ≤ instructionBound ys.length B := by
  induction ys generalizing mask with
  | nil => simp [steps,instructionBound]
  | cons y ys ih =>
    cases mask with
    | nil => simp [steps,instructionBound]
    | cons enabled fs =>
      have hi := ih fs (fun z hz => loads z (List.mem_cons_of_mem _ hz))
      have he := entry_steps_bound enabled amount y B amt (loads y List.mem_cons_self)
      simp only [steps,instructionBound,List.length_cons] at *
      nlinarith

theorem result_width (amount : Fraction) (ys : List Fraction) (mask : List Bool) (B : ℕ)
    (amt : StoredBounded amount B) (loads : ∀ x∈ys,StoredBounded x B) :
    ∀ z∈result amount ys mask,StoredBounded z (2*B+3) := by
  induction ys generalizing mask with
  | nil => simp [result]
  | cons y ys ih =>
    cases mask with
    | nil => simp [result]
    | cons enabled fs =>
      intro z hz
      simp only [result,List.mem_cons] at hz
      rcases hz with rfl | hz
      · have hb := add_stored_bounded (stored_raw_bound (loads y List.mem_cons_self))
          (stored_raw_bound (operand_width enabled amount B amt))
        simpa only [PackingLoadEntry.result,show B+(B+1)+2=2*B+3 by omega] using hb
      · exact ih fs (fun z hz => loads z (List.mem_cons_of_mem _ hz)) z hz
end DirectedFlowCutGap.PackingLoadRow
