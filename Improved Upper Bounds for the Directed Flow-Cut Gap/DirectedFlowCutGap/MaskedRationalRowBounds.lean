import DirectedFlowCutGap.MaskedRationalRowTrace

namespace DirectedFlowCutGap.MaskedRationalRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem row_high {xs : List Fraction} {mask : List Bool} (initial : NaturalState 24)
    (pc0 : initial.pc=22) (hn : initial.next=initial.heap.length)
    (row : StoredList initial.heap initial.registers.a xs)
    (flags : BoolList initial.heap initial.registers.b mask)
    (aligned : xs.length=mask.length) (empty : initial.stack=[]) :
    ∃ ext root,ext.length=cells mask ∧
      NaturalRun program (1+steps mask) initial []
        (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a
          initial.registers.b initial.registers.c root [] initial.source 23) ∧
      StoredList (initial.heap++ext) root (result xs mask) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn row flags empty
      subst pc;subst stack
      have first : tickNatural program (state heap next a b c d [] source 22)=
          some ⟨state heap next a b c d [⟨23,.r3,⟨a,b,c,d⟩⟩] source 0,[],0⟩ := by
        simp [tickNatural,program,state]
      obtain ⟨ext,root,len,run,rep⟩ := row_return row flags aligned next c d hn ⟨a,b,c,d⟩ 23 [] source
      exact ⟨ext,root,len,by simpa [Nat.add_comm,state] using NaturalRun.step first run,rep⟩

theorem steps_bound (mask : List Bool) : 1+steps mask ≤ 17*mask.length+4 := by
  induction mask with
  | nil => simp [steps]
  | cons b bs ih => cases b <;> simp [steps] at * <;> omega

theorem result_length (xs : List Fraction) (mask : List Bool) (aligned : xs.length=mask.length) :
    (result xs mask).length=xs.length := by simp [result,aligned]

theorem result_width (xs : List Fraction) (mask : List Bool) (B : ℕ)
    (row : ∀ x∈xs,StoredBounded x B) :
    ∀ z∈result xs mask,StoredBounded z (B+1) := by
  induction xs generalizing mask with
  | nil => simp [result]
  | cons x xs ih =>
    cases mask with
    | nil => simp [result]
    | cons enabled bs =>
      intro z hz
      simp only [result,List.zipWith_cons_cons,List.mem_cons] at hz
      rcases hz with rfl | hz
      · cases enabled
        · simp [StoredBounded,BinaryRational.zero]
        · have hx := row x List.mem_cons_self
          exact ⟨hx.1.trans (Nat.le_add_right B 1),hx.2.trans (Nat.le_add_right B 1)⟩
      · exact ih bs (fun q hq => row q (List.mem_cons_of_mem _ hq)) z hz

/-- False mask entries remain literal zero fractions in their original positions. -/
theorem sum_result_eq_length {m : ℕ} (y : BinaryFractionalRows.Row m) (mask : Vector Bool m) :
    (BinaryFractionalRows.sum (result y.toList mask.toList)).1=(BinaryFractionalRows.length y mask).1 := by
  have hv : Vector.zipWith (fun x enabled => if enabled then x else BinaryRational.zero) y mask=
      Vector.ofFn (fun i : Fin m => if mask[i.val] then BinaryFractionalRows.get y i else BinaryRational.zero) := by
    ext i hi
    simp [BinaryFractionalRows.get]
  unfold BinaryFractionalRows.length
  dsimp only
  rw [EncodedRoundingInput.tabulate_value,←hv]
  simp [result]
end DirectedFlowCutGap.MaskedRationalRow
