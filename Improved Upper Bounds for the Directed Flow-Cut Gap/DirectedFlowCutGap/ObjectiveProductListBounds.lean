import DirectedFlowCutGap.ObjectiveProductListTrace

namespace DirectedFlowCutGap.ObjectiveProductList
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem products_high {xs ys : List Fraction} (initial : NaturalState 150)
    (pc0 : initial.pc=148) (hn : initial.next=initial.heap.length)
    (left : StoredList initial.heap initial.registers.a xs)
    (right : StoredList initial.heap initial.registers.b ys) (aligned : xs.length=ys.length)
    (empty : initial.stack=[]) :
    ∃ ext root,ext.length=cells xs ys ∧
      NaturalRun program (1+steps xs ys) initial []
        (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a
          initial.registers.b initial.registers.c root [] initial.source 149) ∧
      StoredList (initial.heap++ext) root (products xs ys) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn left right empty
      subst pc;subst stack
      have first : tickNatural program (state heap next a b c d [] source 148)=
          some ⟨state heap next a b c d [⟨149,.r3,⟨a,b,c,d⟩⟩] source 132,[],0⟩ := by
        simp [tickNatural,program,state]
      obtain ⟨ext,root,len,run,rep⟩ := products_return left right aligned next c d hn ⟨a,b,c,d⟩ 149 [] source
      exact ⟨ext,root,len,by simpa [Nat.add_comm,state] using NaturalRun.step first run,rep⟩

def instructionBound (n B : ℕ) : ℕ := n*(500*(4*B+2)^2+15)+4

theorem steps_bound (xs ys : List Fraction) (B : ℕ)
    (aligned : xs.length=ys.length)
    (hx : ∀ x∈xs,StoredBounded x B) (hy : ∀ y∈ys,StoredBounded y B) :
    1+steps xs ys≤ instructionBound xs.length B := by
  induction xs generalizing ys with
  | nil => simp [steps,instructionBound]
  | cons x xs ih =>
    cases ys with
    | nil => simp at aligned
    | cons y ys =>
      have al : xs.length=ys.length := by simpa using aligned
      have hi := ih ys al (fun z hz => hx z (List.mem_cons_of_mem _ hz))
        (fun z hz => hy z (List.mem_cons_of_mem _ hz))
      obtain ⟨xn,xd⟩ := hx x List.mem_cons_self
      obtain ⟨yn,yd⟩ := hy y List.mem_cons_self
      have size : CanonicalRationalProduct.inputSize x y≤4*B+2 := by
        unfold CanonicalRationalProduct.inputSize;omega
      have hp := (CanonicalRationalProduct.instructions_bound x y).trans
        (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left size 2))
      simp only [steps,instructionBound,List.length_cons] at *
      nlinarith

theorem products_length (xs ys : List Fraction) (aligned : xs.length=ys.length) :
    (products xs ys).length=xs.length := by simp [products,aligned]

theorem products_width (xs ys : List Fraction) (B : ℕ)
    (hx : ∀ x∈xs,StoredBounded x B) (hy : ∀ y∈ys,StoredBounded y B) :
    ∀ z∈products xs ys,StoredBounded z (B+B+1) := by
  induction xs generalizing ys with
  | nil => simp [products]
  | cons x xs ih =>
    cases ys with
    | nil => simp [products]
    | cons y ys =>
      have hp := BinaryRational.mul_stored_bounded
        (BinaryFractionalRows.stored_raw_bound (hx x List.mem_cons_self))
        (BinaryFractionalRows.stored_raw_bound (hy y List.mem_cons_self))
      intro z hz
      simp only [products,List.zipWith_cons_cons,List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hp
      · exact ih ys (fun q hq => hx q (List.mem_cons_of_mem _ hq))
          (fun q hq => hy q (List.mem_cons_of_mem _ hq)) z hz
end DirectedFlowCutGap.ObjectiveProductList
