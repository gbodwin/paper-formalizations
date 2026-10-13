import DirectedFlowCutGap.AdaptivePackingArithmeticCalls

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

theorem comparison_return (x y : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 4800) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext root,ext.length=RationalComparisonProgram.cells x y ∧
      NaturalRun program (RationalComparisonProgram.instructions x y+1)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 3486) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (BinaryRational.le x y).1) := by
  obtain ⟨out,high,flag,_,_,src,frames,hpc,dense,⟨ext,he,len⟩,_⟩ :=
    RationalComparisonProgram.run_high x y
      (RationalComparisonProgram.state heap next a b c d [] source 144) rfl hn left right rfl
  have shape : out=⟨heap++ext,next+ext.length,out.registers,[],157,source⟩ := by
    cases out
    simp_all [RationalComparisonProgram.state]
  rw [shape] at high flag
  have run := call_run comparisonLabel RationalComparisonProgram.program comparison_slots high
    (by simp [program,comparisonLabel,RationalComparisonProgram.program,callable]) saved pc stack
  refine ⟨ext,out.registers.d,len,?_,flag⟩
  simpa [state,RationalComparisonProgram.state,comparisonLabel] using run

theorem addition_return (x y : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 4800) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext root,ext.length=CanonicalRationalAddition.cells x y ∧
      NaturalRun program (CanonicalRationalAddition.instructions x y+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 4160) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryRational.add x y).1 := by
  obtain ⟨ext,root,len,high,rep⟩ := CanonicalRationalAddition.add_high x y
    (CanonicalRationalAddition.state heap next a b c d [] source 140) rfl hn left right rfl
  have run := call_run additionLabel CanonicalRationalAddition.program addition_slots high
    (by simp [program,additionLabel,CanonicalRationalAddition.program,callable]) saved pc stack
  refine ⟨ext,root,len,?_,rep⟩
  convert run using 1 <;> simp [state,additionLabel,Nat.add_assoc]
  omega

theorem amount_return {n : ℕ} (capacity : Row n) (q : BinaryFractionalCore.Choice n)
    (labels : Fin n → Bits) (numeric : ∀ j,value (labels j)=j.val)
    {heap : NaturalHeap} {a b : ℕ} (choice : OracleChoice.StoredChoice heap a labels q)
    (table : CanonicalRationalSum.StoredList heap b capacity.toList)
    (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 4800) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext root,ext.length=q.bottleneck.val+2 ∧
      NaturalRun program (BinaryIndexedPairRead.steps (labels q.bottleneck)+7)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 2654) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (get capacity q.bottleneck) := by
  obtain ⟨ext,root,index,len,high,rep,_⟩ := PackingAmount.choice_high capacity q labels numeric
    (PackingAmount.state heap next a b c d [] source 40) rfl hn rfl choice table
  have run := call_run amountLabel PackingAmount.program amount_slots high
    (by simp [program,amountLabel,PackingAmount.program,callable]) saved pc stack
  refine ⟨ext,root,len,?_,rep⟩
  simpa [state,amountLabel,PackingAmount.state,Nat.add_assoc] using run
end DirectedFlowCutGap.AdaptivePackingState
