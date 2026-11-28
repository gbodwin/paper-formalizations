import OnlineReachabilityPreservers.SteinerBinaryRangeMachine

/-! Finite stack execution of aligned binary addition with an initial carry. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private def addAlignedDigits : List (Bool × Bool) → Bool → List Bool
  | [],carry => if carry then [true] else []
  | (x,y)::digits,carry => sumBit x y carry :: addAlignedDigits digits (carryBit x y carry)

private theorem addAlignedDigits_length_le (digits : List (Bool × Bool)) (carry : Bool) :
    (addAlignedDigits digits carry).length ≤ digits.length+1 := by
  induction digits generalizing carry with
  | nil => cases carry <;> decide
  | cons pair digits ih =>
    rcases pair with ⟨x,y⟩
    have remainder := ih (carryBit x y carry)
    simp only [addAlignedDigits,List.length_cons]
    omega

private theorem addAlignedDigits_eq_binaryAdd (left right : List Bool) (carry : Bool) :
    addAlignedDigits (alignBinaryDigits left right) carry = (addBinaryWordsWithWork left right carry).1 := by
  induction total : left.length+right.length using Nat.strong_induction_on generalizing left right carry with
  | h size smaller =>
    by_cases empty : left = [] ∧ right = []
    · obtain ⟨rfl,rfl⟩ := empty
      simp [alignBinaryDigits,addAlignedDigits,addBinaryWordsWithWork]
    have shorter : left.tail.length+right.tail.length < size := by
      cases left <;> cases right <;> simp_all <;> omega
    rw [alignBinaryDigits_cons empty,addAlignedDigits,addBinaryWordsWithWork,dite_eq_right empty]
    exact congrArg (List.cons (sumBit (left.headD false) (right.headD false) carry))
      (smaller _ shorter left.tail right.tail _ rfl)

private abbrev AdderSymbol := Bool × Bool
private abbrev AdderRegister := Bool × Option AdderSymbol
private abbrev AdderStmt := Turing.TM2.Stmt (fun _ : Bool => AdderSymbol) (Fin 3) AdderRegister

private def adderObserve (r : AdderRegister) (seen : Option AdderSymbol) : AdderRegister :=
  (r.1,seen)

private def adderMachineProgram (label : Fin 3) : AdderStmt :=
  if label = 0 then
    pop false (fun _ symbol => ((symbol.getD (false,false)).1,none)) (goto fun _ => 1)
  else if label = 1 then
    peek false adderObserve <|
      branch (fun r => r.2.isSome)
        (pop false adderObserve <|
          push true (fun r =>
            let bits := r.2.getD (false,false)
            (sumBit bits.1 bits.2 r.1,false)) <|
          load (fun r =>
            let bits := r.2.getD (false,false)
            (carryBit bits.1 bits.2 r.1,none)) <| goto (fun _ => 1))
        (branch Prod.fst
          (push true (fun _ => (true,false)) <| load (fun _ => (false,none)) <| goto (fun _ => 2))
          (goto fun _ => 2))
  else
    peek true adderObserve <|
      branch (fun r => r.2.isSome)
        (pop true adderObserve <| push false (fun r => r.2.getD (false,false)) <|
          load (fun _ => (false,none)) <| goto (fun _ => 2))
        halt

/-- A two-stack machine reads the carry header and aligned bit pairs,
buffers their sum bits, and restores the low-bit-first output order. -/
abbrev steinerBinaryAdditionMachine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ _ := AdderSymbol
  Λ := Fin 3
  main := 0
  σ := AdderRegister
  initialState := (false,none)
  m := adderMachineProgram

private def adderStacks (tape buffer : List AdderSymbol) (stack : Bool) : List AdderSymbol :=
  if stack then buffer else tape

private def adderConfig (label : Option (Fin 3)) (carry : Bool) (tape buffer : List AdderSymbol) :
    steinerBinaryAdditionMachine.Cfg where
  l := label
  var := (carry,none)
  stk := adderStacks tape buffer

private theorem adderStacks_tape (tape buffer new : List AdderSymbol) :
    Function.update (adderStacks tape buffer) false new = adderStacks new buffer := by
  funext stack
  cases stack <;> simp [adderStacks]

private theorem adderStacks_buffer (tape buffer new : List AdderSymbol) :
    Function.update (adderStacks tape buffer) true new = adderStacks tape new := by
  funext stack
  cases stack <;> simp [adderStacks]

private theorem adderStep_read_carry (carry : Bool) (digits buffer : List AdderSymbol) :
    steinerBinaryAdditionMachine.step (adderConfig (some 0) false ((carry,false)::digits) buffer) =
      some (adderConfig (some 1) carry digits buffer) := by
  simp [FinTM2.step,steinerBinaryAdditionMachine,adderConfig,Turing.TM2.step,Turing.TM2.stepAux,
    adderMachineProgram,adderStacks_tape,adderStacks]
  rfl

private theorem adderStep_one_digit (x y carry : Bool) (digits buffer : List AdderSymbol) :
    steinerBinaryAdditionMachine.step (adderConfig (some 1) carry ((x,y)::digits) buffer) =
      some (adderConfig (some 1) (carryBit x y carry) digits ((sumBit x y carry,false)::buffer)) := by
  simp [FinTM2.step,steinerBinaryAdditionMachine,adderConfig,Turing.TM2.step,Turing.TM2.stepAux,
    adderMachineProgram,adderObserve,adderStacks_tape,adderStacks_buffer,adderStacks]
  rfl

private theorem adderStep_end_digits (carry : Bool) (buffer : List AdderSymbol) :
    steinerBinaryAdditionMachine.step (adderConfig (some 1) carry [] buffer) =
      some (adderConfig (some 2) false [] (if carry then (true,false)::buffer else buffer)) := by
  cases carry <;>
    simp [FinTM2.step,steinerBinaryAdditionMachine,adderConfig,Turing.TM2.step,Turing.TM2.stepAux,
      adderMachineProgram,adderObserve,adderStacks_buffer,adderStacks] <;> rfl

private theorem adderStep_restore (digit : AdderSymbol) (tape buffer : List AdderSymbol) :
    steinerBinaryAdditionMachine.step (adderConfig (some 2) false tape (digit::buffer)) =
      some (adderConfig (some 2) false (digit::tape) buffer) := by
  simp [FinTM2.step,steinerBinaryAdditionMachine,adderConfig,Turing.TM2.step,Turing.TM2.stepAux,
    adderMachineProgram,adderObserve,adderStacks_tape,adderStacks_buffer,adderStacks]
  rfl

private theorem adderStep_halt (tape : List AdderSymbol) :
    steinerBinaryAdditionMachine.step (adderConfig (some 2) false tape []) =
      some (adderConfig none false tape []) := by
  simp [FinTM2.step,steinerBinaryAdditionMachine,adderConfig,Turing.TM2.step,Turing.TM2.stepAux,
    adderMachineProgram,adderObserve,adderStacks]
  rfl

private def adderSingleStep {a b : steinerBinaryAdditionMachine.Cfg}
    (step : steinerBinaryAdditionMachine.step a = some b) :
    EvalsToInTime steinerBinaryAdditionMachine.step a (some b) 1 where
  steps := 1
  evals_in_steps := by change steinerBinaryAdditionMachine.step a = some b; exact step
  steps_le_m := le_rfl

/-- Store each answer bit in the first component of an alphabet symbol. -/
def encodeSteinerBinarySum (bits : List Bool) : List (Bool × Bool) :=
  bits.map fun bit => (bit,false)

private def adderComputeDigits (digits : List AdderSymbol) (buffer : List AdderSymbol) (carry : Bool) :
    EvalsToInTime steinerBinaryAdditionMachine.step (adderConfig (some 1) carry digits buffer)
      (some (adderConfig (some 2) false [] ((encodeSteinerBinarySum (addAlignedDigits digits carry)).reverse ++ buffer)))
      (digits.length+1) := by
  induction digits generalizing buffer carry with
  | nil =>
    cases carry with
    | false =>
      simpa [addAlignedDigits,encodeSteinerBinarySum] using adderSingleStep (adderStep_end_digits false buffer)
    | true =>
      simpa [addAlignedDigits,encodeSteinerBinarySum] using adderSingleStep (adderStep_end_digits true buffer)
  | cons digit digits ih =>
    rcases digit with ⟨x,y⟩
    have first := adderSingleStep (adderStep_one_digit x y carry digits buffer)
    have rest := ih ((sumBit x y carry,false)::buffer) (carryBit x y carry)
    have both := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [List.length_cons,addAlignedDigits,encodeSteinerBinarySum,List.map_cons,List.reverse_cons,
      List.append_assoc,List.singleton_append] using both

private def adderRestoreBits (bits tape : List AdderSymbol) :
    EvalsToInTime steinerBinaryAdditionMachine.step (adderConfig (some 2) false tape bits)
      (some (adderConfig none false (bits.reverse++tape) [])) (bits.length+1) := by
  induction bits generalizing tape with
  | nil => simpa using adderSingleStep (adderStep_halt tape)
  | cons bit bits ih =>
    have first := adderSingleStep (adderStep_restore bit tape bits)
    have both := EvalsToInTime.trans _ _ _ _ _ _ first (ih (bit::tape))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using both

private theorem adderMachine_init (tape : List AdderSymbol) :
    initList steinerBinaryAdditionMachine tape = adderConfig (some 0) false tape [] := by
  unfold initList adderConfig
  apply congrArg (fun stk : Bool → List AdderSymbol =>
    (⟨some (0:Fin 3),(false,none),stk⟩ : steinerBinaryAdditionMachine.Cfg))
  funext stack
  cases stack <;> rfl

private theorem adderMachine_halt (output : List AdderSymbol) :
    haltList steinerBinaryAdditionMachine output = adderConfig none false output [] := by
  unfold haltList adderConfig
  apply congrArg (fun stk : Bool → List AdderSymbol =>
    (⟨none,(false,none),stk⟩ : steinerBinaryAdditionMachine.Cfg))
  funext stack
  cases stack <;> rfl

/-- Supply a carry header and low-bit-first digit pairs, padded with false. -/
def encodeSteinerBinaryAddition (request : List Bool × List Bool × Bool) : List (Bool × Bool) :=
  (request.2.2,false)::alignBinaryDigits request.1 request.2.1

def steinerBinaryAdditionAnswer (request : List Bool × List Bool × Bool) : List Bool :=
  (addBinaryWordsWithWork request.1 request.2.1 request.2.2).1

/-- The machine returns the exact sum word of the existing bit adder,
within a linear bound in the aligned digit count. -/
def steinerBinaryAdditionMachine_run (request : List Bool × List Bool × Bool) :
    TM2OutputsInTime steinerBinaryAdditionMachine (encodeSteinerBinaryAddition request)
      (some (encodeSteinerBinarySum (steinerBinaryAdditionAnswer request)))
      (2*(encodeSteinerBinaryAddition request).length+2) := by
  rcases request with ⟨left,right,carry⟩
  let digits := alignBinaryDigits left right
  let output := encodeSteinerBinarySum (addAlignedDigits digits carry)
  have first := adderSingleStep (adderStep_read_carry carry digits [])
  have compute := adderComputeDigits digits [] carry
  rw [List.append_nil] at compute
  have restore := adderRestoreBits output.reverse []
  rw [List.reverse_reverse,List.append_nil,List.length_reverse] at restore
  have combined := EvalsToInTime.trans _ _ _ _ _ _ first compute
  have all := EvalsToInTime.trans _ _ _ _ _ _ combined restore
  have paid := all.steps_le_m
  have outputLen : output.length ≤ digits.length+1 := by
    simpa only [output,encodeSteinerBinarySum,List.length_map] using addAlignedDigits_length_le digits carry
  have enough : all.steps ≤ 2*(encodeSteinerBinaryAddition (left,right,carry)).length+2 := by
    change all.steps ≤ 2*(digits.length+1)+2
    omega
  unfold TM2OutputsInTime
  change EvalsToInTime steinerBinaryAdditionMachine.step _
    (some (haltList steinerBinaryAdditionMachine _)) _
  rw [adderMachine_init,adderMachine_halt]
  have exactOutput : output = encodeSteinerBinarySum (steinerBinaryAdditionAnswer (left,right,carry)) := by
    simp only [output,digits,steinerBinaryAdditionAnswer,addAlignedDigits_eq_binaryAdd]
  rw [← exactOutput]
  exact ⟨all.toEvalsTo,enough⟩

/-- The output word decodes to the two input values plus the incoming carry. -/
theorem steinerBinaryAdditionAnswer_value (request : List Bool × List Bool × Bool) :
    binaryWordValue (steinerBinaryAdditionAnswer request) =
      binaryWordValue request.1+binaryWordValue request.2.1+(if request.2.2 then 1 else 0) :=
  (addBinaryWordsWithWork_spec request.1 request.2.1 request.2.2).1

/-- The adder has a linear transition bound in the two supplied word lengths. -/
def steinerBinaryAdditionMachine_word_lengths (request : List Bool × List Bool × Bool) :
    TM2OutputsInTime steinerBinaryAdditionMachine (encodeSteinerBinaryAddition request)
      (some (encodeSteinerBinarySum (steinerBinaryAdditionAnswer request)))
      (2*(request.1.length+request.2.1.length)+4) := by
  have run := steinerBinaryAdditionMachine_run request
  have aligned := alignBinaryDigits_length_le request.1 request.2.1
  have bound : 2*(encodeSteinerBinaryAddition request).length+2 ≤ 2*(request.1.length+request.2.1.length)+4 := by
    simp only [encodeSteinerBinaryAddition,List.length_cons]
    omega
  exact ⟨run.toEvalsTo,run.steps_le_m.trans bound⟩

/-- The supplied carry and padded pairs give a linear polynomial
certificate in Mathlib's stack-machine model. -/
noncomputable def steinerBinaryAdditionMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerBinaryAddition encodeSteinerBinarySum steinerBinaryAdditionAnswer where
  tm := steinerBinaryAdditionMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2*Polynomial.X+Polynomial.C 2
  outputsFun request := by
    change TM2OutputsInTime steinerBinaryAdditionMachine ((encodeSteinerBinaryAddition request).map id)
      (some ((encodeSteinerBinarySum (steinerBinaryAdditionAnswer request)).map id)) _
    simpa only [List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_X,
      Polynomial.eval_C] using steinerBinaryAdditionMachine_run request

end OnlineReachabilityPreservers
