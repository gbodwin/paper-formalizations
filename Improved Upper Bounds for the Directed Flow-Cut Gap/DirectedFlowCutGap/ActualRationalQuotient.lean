import DirectedFlowCutGap.CanonicalRationalQuotientReturn

namespace DirectedFlowCutGap.CanonicalRationalQuotient
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

/-- A real top-level caller removes the supplied return-frame premise. -/
theorem quotient_high (x y : BinaryRational.Fraction) (initial : NaturalState 164)
    (pc0 : initial.pc=161) (hn : initial.next=initial.heap.length)
    (left : Stored initial.heap initial.registers.a x)
    (right : Stored initial.heap initial.registers.b y) (empty : initial.stack=[]) :
    ∃ ext root, ext.length=cells x y ∧
      NaturalRun program (1+steps x y) initial []
        (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a
          initial.registers.b initial.registers.c root [] initial.source 162) ∧
      Stored (initial.heap++ext) root (BinaryRational.div x y).1 := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn left right empty
      subst pc;subst stack
      have first : tickNatural program (state heap next a b c d [] source 161)=
          some ⟨state heap next a b c d [⟨162,.r3,⟨a,b,c,d⟩⟩] source 144,[],0⟩ := by
        simp [tickNatural,program,state]
      obtain ⟨ext,root,len,run,rep⟩ := quotient_return x y left right next c d hn ⟨a,b,c,d⟩ 162 [] source
      exact ⟨ext,root,len,by simpa [Nat.add_comm,state] using NaturalRun.step first run,rep⟩

def inputSize (x y : BinaryRational.Fraction) : ℕ :=
  x.num.length+x.den.length+y.num.length+y.den.length+2

theorem cross_bound (x y : BinaryRational.Fraction) :
    crossSteps x y ≤ 500*(inputSize x y)^2 := by
  let z := inputSize x y
  have hz : 2≤z := by dsimp [z,inputSize];omega
  have hn : x.num.length+y.den.length+2≤z := by dsimp [z,inputSize];omega
  have hd : x.den.length+y.num.length+2≤z := by dsimp [z,inputSize];omega
  have h1 := (CanonicalArithmeticProgram.instructions_bound true x.num y.den).trans
    (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left hn 2))
  have h2 := (CanonicalArithmeticProgram.instructions_bound true x.den y.num).trans
    (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left hd 2))
  dsimp only [crossSteps]
  change _≤500*z^2
  nlinarith

theorem steps_bound (x y : BinaryRational.Fraction) :
    1+steps x y ≤ 600*(inputSize x y)^2 := by
  have hc := cross_bound x y
  have hz := BinaryZeroProgram.steps_bound y.num
  have hlen : y.num.length≤ inputSize x y := by unfold inputSize;omega
  have hpos : 2≤ inputSize x y := by unfold inputSize;omega
  unfold steps
  split <;> nlinarith

/-- The exact original rational primitive is realized in the same lower heap,
with all scratch arithmetic, original records and one paid terminal halt. -/
theorem quotient_bit (x y : BinaryRational.Fraction) {H B : ℕ} (initial : BitState 164)
    (bounded : initial.Bounded H B) (pc0 : initial.pc=161)
    (hn : value initial.next=initial.heap.length)
    (left : Stored (eraseState initial).heap (eraseState initial).registers.a x)
    (right : Stored (eraseState initial).heap (eraseState initial).registers.b y)
    (empty : initial.stack=[]) :
    ∃ charge out, Run program (1+steps x y) charge initial [] out ∧
      Stored (eraseState out).heap (eraseState out).registers.d (BinaryRational.div x y).1 ∧
      Stored (eraseState out).heap (eraseState initial).registers.a x ∧
      Stored (eraseState out).heap (eraseState initial).registers.b y ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=162 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells x y) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 164 H B (600*(inputSize x y)^2) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have hs : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,root,len,high,rep⟩ := quotient_high x y (eraseState initial) pc0 hn' left right hs
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have halt : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have hn : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          (eraseState initial).registers.a (eraseState initial).registers.b
          (eraseState initial).registers.c root [] (eraseState initial).source 162)=none := rfl
    rw [hn] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  have cost := (terminal_accounting run bounded halt).2
  have hb := steps_bound x y
  have hm : completeBound 164 H B (1+steps x y) ≤
      completeBound 164 H B (600*(inputSize x y)^2) := by
    unfold completeBound runBound stepBound
    gcongr
  refine ⟨charge,out,run,?_,?_,?_,source,?_,?_,⟨ext,?_,len⟩,halt,cost.trans hm⟩
  · rw [erase];exact rep
  · rw [erase];exact stored_extend left ext
  · rw [erase];exact stored_extend right ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=162 := by rw [erase];rfl
    exact h
  · rw [erase];rfl


end DirectedFlowCutGap.CanonicalRationalQuotient
