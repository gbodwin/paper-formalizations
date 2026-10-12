import DirectedFlowCutGap.PackingUpdateRowTrace

namespace DirectedFlowCutGap.PackingUpdateRow
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem row_high (amount : Fraction) {cs ys : List Fraction} {mask : List Bool}
    (initial : NaturalState 520) (pc0 : initial.pc=518) (hn : initial.next=initial.heap.length)
    (cap : StoredList initial.heap initial.registers.a cs)
    (weights : StoredList initial.heap initial.registers.b ys)
    {mr ar : ℕ} (flags : BoolList initial.heap mr mask) (amt : Stored initial.heap ar amount)
    (context : initial.heap[initial.registers.c]?=some (.pair mr ar))
    (aligned : cs.length=ys.length) (alignedMask : cs.length=mask.length)
    (empty : initial.stack=[]) :
    ∃ ext root,ext.length=cells amount cs ys mask ∧
      NaturalRun program (1+steps amount cs ys mask) initial []
        (state (initial.heap++ext) (initial.next+ext.length) root initial.registers.b
          initial.registers.c initial.registers.d [] initial.source 519) ∧
      StoredList (initial.heap++ext) root (result amount cs ys mask) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn cap weights flags amt context empty
      subst pc;subst stack
      have first : tickNatural program (state heap next a b c d [] source 518)=
          some ⟨state heap next a b c d [⟨519,.r0,⟨a,b,c,d⟩⟩] source 480,[],0⟩ := by
        simp [tickNatural,program,state]
      obtain ⟨ext,root,len,run,rep⟩ := row_return amount cap weights flags amt context aligned alignedMask
        next d hn ⟨a,b,c,d⟩ 519 [] source
      exact ⟨ext,root,len,by simpa [Nat.add_comm,state] using NaturalRun.step first run,rep⟩

def instructionBound (n B : ℕ) : ℕ := n*(PackingEntry.instructionBound B+32)+4

theorem steps_bound (amount : Fraction) (cs ys : List Fraction) (mask : List Bool) (B : ℕ)
    (amt : StoredBounded amount B) (cap : ∀ x∈cs,StoredBounded x B)
    (weights : ∀ x∈ys,StoredBounded x B) :
    1+steps amount cs ys mask ≤ instructionBound cs.length B := by
  induction cs generalizing ys mask with
  | nil => simp [steps,instructionBound]
  | cons ci cs ih =>
    cases ys with
    | nil => simp [steps,instructionBound]
    | cons y ys =>
      cases mask with
      | nil => simp [steps,instructionBound]
      | cons enabled fs =>
        have hi := ih ys fs (fun z hz => cap z (List.mem_cons_of_mem _ hz))
          (fun z hz => weights z (List.mem_cons_of_mem _ hz))
        have he := PackingEntry.steps_bound ci amount y B (cap ci List.mem_cons_self) amt
          (weights y List.mem_cons_self)
        simp only [steps,instructionBound,List.length_cons] at *
        split <;> nlinarith

theorem result_width (amount : Fraction) (cs ys : List Fraction) (mask : List Bool) (B : ℕ)
    (amt : StoredBounded amount B) (cap : ∀ x∈cs,StoredBounded x B)
    (weights : ∀ x∈ys,StoredBounded x B) :
    ∀ z∈result amount cs ys mask,StoredBounded z (3*B+8) := by
  induction cs generalizing ys mask with
  | nil => simp [result]
  | cons ci cs ih =>
    cases ys with
    | nil => simp [result]
    | cons y ys =>
      cases mask with
      | nil => simp [result]
      | cons enabled fs =>
        have hi := ih ys fs (fun z hz => cap z (List.mem_cons_of_mem _ hz))
          (fun z hz => weights z (List.mem_cons_of_mem _ hz))
        intro z hz
        simp only [result,List.mem_cons] at hz
        rcases hz with rfl | hz
        · cases enabled with
          | false =>
            have hy := weights y List.mem_cons_self
            exact ⟨by simpa using hy.1.trans (by omega : B≤3*B+8),
              by simpa using hy.2.trans (by omega : B≤3*B+8)⟩
          | true => exact (PackingEntry.widths ci amount y B (cap ci List.mem_cons_self) amt
              (weights y List.mem_cons_self)).2.2.2
        · exact hi z hz
end DirectedFlowCutGap.PackingUpdateRow
