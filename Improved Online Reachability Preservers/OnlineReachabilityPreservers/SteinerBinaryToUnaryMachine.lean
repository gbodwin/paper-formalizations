import OnlineReachabilityPreservers.SteinerBinaryRangeMachine
import OnlineReachabilityPreservers.SteinerUnaryProductMachine

/-! Convert a least-significant-bit-first word to unary in time linear
in the word length and its numerical value. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private inductive BinaryUnaryLabel where
  | reverse
  | digit
  | double
  | restore
  deriving DecidableEq

private instance : Fintype BinaryUnaryLabel where
  elems := {.reverse,.digit,.double,.restore}
  complete := by intro label; cases label <;> simp

private abbrev BinaryUnaryRegister := Option Bool
private abbrev BinaryUnaryProgram :=
  Turing.TM2.Stmt (fun _ : Fin 4 => Bool) BinaryUnaryLabel BinaryUnaryRegister

private def binaryUnaryObserve (_ : BinaryUnaryRegister) (bit : Option Bool) : BinaryUnaryRegister := bit

private def binaryUnaryNext (label : BinaryUnaryLabel) : BinaryUnaryProgram :=
  load (fun _ => none) (goto (fun _ => label))

private def binaryUnaryProgram : BinaryUnaryLabel → BinaryUnaryProgram
  | .reverse =>
    pop 0 binaryUnaryObserve <|
      branch Option.isSome
        (push 1 (·.getD false) (binaryUnaryNext .reverse))
        (binaryUnaryNext .digit)
  | .digit =>
    pop 1 binaryUnaryObserve <|
      branch Option.isSome
        (branch (·.getD false)
          (push 3 (fun _ => true) (binaryUnaryNext .double))
          (binaryUnaryNext .double))
        (load (fun _ => none) halt)
  | .double =>
    pop 2 binaryUnaryObserve <|
      branch Option.isSome
        (push 3 (fun _ => true) (push 3 (fun _ => true) (binaryUnaryNext .double)))
        (binaryUnaryNext .restore)
  | .restore =>
    pop 3 binaryUnaryObserve <|
      branch Option.isSome
        (push 2 (fun _ => true) (binaryUnaryNext .restore))
        (binaryUnaryNext .digit)

/-- Reverse low-first input and scan it from its high end. Each digit
doubles the unary accumulator and appends a tally if its bit is true. -/
abbrev steinerBinaryToUnaryMachine : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := BinaryUnaryLabel
  main := .reverse
  σ := BinaryUnaryRegister
  initialState := none
  m := binaryUnaryProgram

private abbrev unaryTallies (n : ℕ) := encodeSteinerUnaryProductCount n
private def unaryDigit (b : Bool) : ℕ := if b then 1 else 0

private def binaryUnaryCfg (label : Option BinaryUnaryLabel) (input bits : List Bool) (answer temp : ℕ) :
    steinerBinaryToUnaryMachine.Cfg where
  l := label
  var := none
  stk := ![input,bits,unaryTallies answer,unaryTallies temp]

private theorem binaryUnary_update0 (a b c d word : List Bool) :
    Function.update (![a,b,c,d] : Fin 4 → List Bool) 0 word = ![word,b,c,d] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem binaryUnary_update1 (a b c d word : List Bool) :
    Function.update (![a,b,c,d] : Fin 4 → List Bool) 1 word = ![a,word,c,d] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem binaryUnary_update2 (a b c d word : List Bool) :
    Function.update (![a,b,c,d] : Fin 4 → List Bool) 2 word = ![a,b,word,d] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem binaryUnary_update3 (a b c d word : List Bool) :
    Function.update (![a,b,c,d] : Fin 4 → List Bool) 3 word = ![a,b,c,word] := by
  funext i
  fin_cases i <;> simp [Function.update]

private abbrev BinaryUnaryRun (start finish : steinerBinaryToUnaryMachine.Cfg) (steps : ℕ) : Prop :=
  (flip bind steinerBinaryToUnaryMachine.step)^[steps] (some start) = some finish

private theorem binaryUnary_one {start finish : steinerBinaryToUnaryMachine.Cfg}
    (move : steinerBinaryToUnaryMachine.step start = some finish) : BinaryUnaryRun start finish 1 := move

private theorem binaryUnary_join {start between finish : steinerBinaryToUnaryMachine.Cfg} {a b : ℕ}
    (first : BinaryUnaryRun start between a) (second : BinaryUnaryRun between finish b) :
    BinaryUnaryRun start finish (a+b) := by
  unfold BinaryUnaryRun at *
  rw [Nat.add_comm a b,Function.iterate_add_apply,first]
  exact second

private theorem binaryUnary_reverseBit (bit : Bool) (tail moved : List Bool) :
    BinaryUnaryRun (binaryUnaryCfg (some .reverse) (bit::tail) moved 0 0)
      (binaryUnaryCfg (some .reverse) tail (bit::moved) 0 0) 1 := by
  apply binaryUnary_one
  simp [FinTM2.step,steinerBinaryToUnaryMachine,binaryUnaryCfg,Turing.TM2.step,Turing.TM2.stepAux,
    binaryUnaryProgram,binaryUnaryObserve,binaryUnaryNext,binaryUnary_update0,binaryUnary_update1]
  rfl

private theorem binaryUnary_reverseEnd (moved : List Bool) :
    BinaryUnaryRun (binaryUnaryCfg (some .reverse) [] moved 0 0)
      (binaryUnaryCfg (some .digit) [] moved 0 0) 1 := by
  apply binaryUnary_one
  simp [FinTM2.step,steinerBinaryToUnaryMachine,binaryUnaryCfg,Turing.TM2.step,Turing.TM2.stepAux,
    binaryUnaryProgram,binaryUnaryObserve,binaryUnaryNext,binaryUnary_update0]
  rfl

private theorem binaryUnary_reverse (word moved : List Bool) :
    BinaryUnaryRun (binaryUnaryCfg (some .reverse) word moved 0 0)
      (binaryUnaryCfg (some .digit) [] (word.reverse++moved) 0 0) (word.length+1) := by
  induction word generalizing moved with
  | nil => exact binaryUnary_reverseEnd moved
  | cons bit tail ih =>
    have all := binaryUnary_join (binaryUnary_reverseBit bit tail moved) (ih (bit::moved))
    have paid : 1+(tail.length+1) = tail.length+1+1 := by omega
    simpa only [List.reverse_cons,List.length_cons,List.append_assoc,List.singleton_append,paid] using all

private theorem binaryUnary_digitBit (bit : Bool) (remaining : List Bool) (answer : ℕ) :
    BinaryUnaryRun (binaryUnaryCfg (some .digit) [] (bit::remaining) answer 0)
      (binaryUnaryCfg (some .double) [] remaining answer (unaryDigit bit)) 1 := by
  apply binaryUnary_one
  cases bit <;> simp [FinTM2.step,steinerBinaryToUnaryMachine,binaryUnaryCfg,Turing.TM2.step,Turing.TM2.stepAux,
    binaryUnaryProgram,binaryUnaryObserve,binaryUnaryNext,binaryUnary_update1,binaryUnary_update3,
    unaryDigit,encodeSteinerUnaryProductCount] <;> rfl

private theorem binaryUnary_digitEnd (answer : ℕ) :
    BinaryUnaryRun (binaryUnaryCfg (some .digit) [] [] answer 0) (binaryUnaryCfg none [] [] answer 0) 1 := by
  apply binaryUnary_one
  simp [FinTM2.step,steinerBinaryToUnaryMachine,binaryUnaryCfg,Turing.TM2.step,Turing.TM2.stepAux,
    binaryUnaryProgram,binaryUnaryObserve,binaryUnaryNext,binaryUnary_update1]
  rfl

private theorem binaryUnary_doubleTally (remaining : List Bool) (answer temp : ℕ) :
    BinaryUnaryRun (binaryUnaryCfg (some .double) [] remaining (answer+1) temp)
      (binaryUnaryCfg (some .double) [] remaining answer (temp+2)) 1 := by
  apply binaryUnary_one
  simp [FinTM2.step,steinerBinaryToUnaryMachine,binaryUnaryCfg,Turing.TM2.step,Turing.TM2.stepAux,
    binaryUnaryProgram,binaryUnaryObserve,binaryUnaryNext,binaryUnary_update2,binaryUnary_update3,
    encodeSteinerUnaryProductCount,List.replicate_succ]
  rfl

private theorem binaryUnary_doubleEnd (remaining : List Bool) (temp : ℕ) :
    BinaryUnaryRun (binaryUnaryCfg (some .double) [] remaining 0 temp)
      (binaryUnaryCfg (some .restore) [] remaining 0 temp) 1 := by
  apply binaryUnary_one
  simp [FinTM2.step,steinerBinaryToUnaryMachine,binaryUnaryCfg,Turing.TM2.step,Turing.TM2.stepAux,
    binaryUnaryProgram,binaryUnaryObserve,binaryUnaryNext,binaryUnary_update2,encodeSteinerUnaryProductCount]
  rfl

private theorem binaryUnary_double (remaining : List Bool) (answer temp : ℕ) :
    BinaryUnaryRun (binaryUnaryCfg (some .double) [] remaining answer temp)
      (binaryUnaryCfg (some .restore) [] remaining 0 (2*answer+temp)) (answer+1) := by
  induction answer generalizing temp with
  | zero => simpa only [Nat.mul_zero,Nat.zero_add] using binaryUnary_doubleEnd remaining temp
  | succ answer ih =>
    have all := binaryUnary_join (binaryUnary_doubleTally remaining answer temp) (ih (temp+2))
    have value : 2*answer+(temp+2) = 2*(answer+1)+temp := by omega
    have paid : 1+(answer+1) = answer+1+1 := by omega
    simpa only [value,paid] using all

private theorem binaryUnary_restoreTally (remaining : List Bool) (answer temp : ℕ) :
    BinaryUnaryRun (binaryUnaryCfg (some .restore) [] remaining answer (temp+1))
      (binaryUnaryCfg (some .restore) [] remaining (answer+1) temp) 1 := by
  apply binaryUnary_one
  simp [FinTM2.step,steinerBinaryToUnaryMachine,binaryUnaryCfg,Turing.TM2.step,Turing.TM2.stepAux,
    binaryUnaryProgram,binaryUnaryObserve,binaryUnaryNext,binaryUnary_update2,binaryUnary_update3,
    encodeSteinerUnaryProductCount,List.replicate_succ]
  rfl

private theorem binaryUnary_restoreEnd (remaining : List Bool) (answer : ℕ) :
    BinaryUnaryRun (binaryUnaryCfg (some .restore) [] remaining answer 0)
      (binaryUnaryCfg (some .digit) [] remaining answer 0) 1 := by
  apply binaryUnary_one
  simp [FinTM2.step,steinerBinaryToUnaryMachine,binaryUnaryCfg,Turing.TM2.step,Turing.TM2.stepAux,
    binaryUnaryProgram,binaryUnaryObserve,binaryUnaryNext,binaryUnary_update3,encodeSteinerUnaryProductCount]
  rfl

private theorem binaryUnary_restore (remaining : List Bool) (answer temp : ℕ) :
    BinaryUnaryRun (binaryUnaryCfg (some .restore) [] remaining answer temp)
      (binaryUnaryCfg (some .digit) [] remaining (answer+temp) 0) (temp+1) := by
  induction temp generalizing answer with
  | zero => simpa only [Nat.add_zero] using binaryUnary_restoreEnd remaining answer
  | succ temp ih =>
    have all := binaryUnary_join (binaryUnary_restoreTally remaining answer temp) (ih (answer+1))
    have value : answer+1+temp = answer+(temp+1) := by omega
    have paid : 1+(temp+1) = temp+1+1 := by omega
    simpa only [value,paid] using all

private theorem binaryUnary_digit (bit : Bool) (remaining : List Bool) (answer : ℕ) :
    BinaryUnaryRun (binaryUnaryCfg (some .digit) [] (bit::remaining) answer 0)
      (binaryUnaryCfg (some .digit) [] remaining (2*answer+unaryDigit bit) 0) (3*answer+unaryDigit bit+3) := by
  have first := binaryUnary_digitBit bit remaining answer
  have doubled := binaryUnary_double remaining answer (unaryDigit bit)
  have restored := binaryUnary_restore remaining 0 (2*answer+unaryDigit bit)
  rw [Nat.zero_add] at restored
  have all := binaryUnary_join (binaryUnary_join first doubled) restored
  have paid : 1+(answer+1)+(2*answer+unaryDigit bit+1) = 3*answer+unaryDigit bit+3 := by omega
  simpa only [paid] using all

private def binaryUnaryValue (answer : ℕ) (bits : List Bool) : ℕ :=
  bits.foldl (fun value bit => 2*value+unaryDigit bit) answer

private theorem binaryUnaryValue_reverse (word : List Bool) :
    binaryUnaryValue 0 word.reverse = binaryWordValue word := by
  induction word with
  | nil => rfl
  | cons bit rest ih =>
    rw [List.reverse_cons]
    unfold binaryUnaryValue at ih ⊢
    rw [List.foldl_append,ih]
    change 2*binaryWordValue rest+unaryDigit bit = binaryWordValue (bit::rest)
    cases bit
    · change 2*binaryWordValue rest+0 = 0+2*binaryWordValue rest
      omega
    · change 2*binaryWordValue rest+1 = 1+2*binaryWordValue rest
      omega

private def binaryUnaryLoopSteps : ℕ → List Bool → ℕ
  | _,[] => 1
  | answer,bit::bits => 3*answer+unaryDigit bit+3+binaryUnaryLoopSteps (2*answer+unaryDigit bit) bits

private theorem binaryUnaryLoop_cost (answer : ℕ) (bits : List Bool) :
    binaryUnaryLoopSteps answer bits+3*answer+2*bits.count true =
      3*binaryUnaryValue answer bits+3*bits.length+1 := by
  induction bits generalizing answer with
  | nil =>
    simp only [binaryUnaryLoopSteps,List.count_nil,List.length_nil,binaryUnaryValue,List.foldl_nil]
    omega
  | cons bit bits ih =>
    have count : (bit::bits).count true = unaryDigit bit+bits.count true := by
      cases bit <;> simp [unaryDigit,Nat.add_comm]
    have next := ih (2*answer+unaryDigit bit)
    rw [binaryUnaryLoopSteps,count]
    simp only [binaryUnaryValue,List.foldl_cons,List.length_cons] at next ⊢
    omega

private theorem binaryUnary_loop (bits : List Bool) (answer : ℕ) :
    BinaryUnaryRun (binaryUnaryCfg (some .digit) [] bits answer 0)
      (binaryUnaryCfg none [] [] (binaryUnaryValue answer bits) 0) (binaryUnaryLoopSteps answer bits) := by
  induction bits generalizing answer with
  | nil => exact binaryUnary_digitEnd answer
  | cons bit bits ih =>
    have all := binaryUnary_join (binaryUnary_digit bit bits answer) (ih (2*answer+unaryDigit bit))
    simpa only [binaryUnaryValue,List.foldl_cons,binaryUnaryLoopSteps] using all

private theorem binaryUnary_init (input : List Bool) :
    initList steinerBinaryToUnaryMachine input = binaryUnaryCfg (some .reverse) input [] 0 0 := by
  apply congrArg (fun stk : Fin 4 → List Bool =>
    (⟨some .reverse,none,stk⟩ : steinerBinaryToUnaryMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem binaryUnary_halt (answer : ℕ) :
    haltList steinerBinaryToUnaryMachine (unaryTallies answer) = binaryUnaryCfg none [] [] answer 0 := by
  apply congrArg (fun stk : Fin 4 → List Bool =>
    (⟨none,none,stk⟩ : steinerBinaryToUnaryMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- Charge reversal and then the accumulator loop. -/
def steinerBinaryToUnarySteps (word : List Bool) : ℕ :=
  word.length+1+binaryUnaryLoopSteps 0 word.reverse

/-- The bit contribution telescopes against successive accumulator
values. Each true bit reduces the exact count by two from the
simpler bound. -/
theorem steinerBinaryToUnarySteps_eq (word : List Bool) :
    steinerBinaryToUnarySteps word+2*word.count true = 4*word.length+3*binaryWordValue word+2 := by
  have work := binaryUnaryLoop_cost 0 word.reverse
  rw [binaryUnaryValue_reverse,List.length_reverse,List.count_reverse] at work
  unfold steinerBinaryToUnarySteps
  omega

/-- Convert every low-first word, including padded words and the empty word. -/
def steinerBinaryToUnaryMachine_run (word : List Bool) :
    TM2OutputsInTime steinerBinaryToUnaryMachine word
      (some (encodeSteinerUnaryProductCount (binaryWordValue word))) (steinerBinaryToUnarySteps word) where
  steps := steinerBinaryToUnarySteps word
  steps_le_m := le_rfl
  evals_in_steps := by
    have reversed := binaryUnary_reverse word []
    rw [List.append_nil] at reversed
    have all := binaryUnary_join reversed (binaryUnary_loop word.reverse 0)
    change BinaryUnaryRun (initList steinerBinaryToUnaryMachine word)
      (haltList steinerBinaryToUnaryMachine (unaryTallies (binaryWordValue word))) _
    rw [binaryUnary_init,binaryUnary_halt,← binaryUnaryValue_reverse]
    exact all

theorem steinerBinaryToUnaryMachine_steps (word : List Bool) :
    (steinerBinaryToUnaryMachine_run word).steps = steinerBinaryToUnarySteps word := rfl

/-- The unary conversion takes time linear in word length and value. -/
def steinerBinaryToUnaryMachine_value_time (word : List Bool) :
    TM2OutputsInTime steinerBinaryToUnaryMachine word
      (some (encodeSteinerUnaryProductCount (binaryWordValue word))) (4*word.length+3*binaryWordValue word+2) :=
  let run := steinerBinaryToUnaryMachine_run word
  ⟨run.toEvalsTo,run.steps_le_m.trans (by have paid := steinerBinaryToUnarySteps_eq word; omega)⟩

/-- An accepted graph endpoint converts to its exact index within time
linear in the endpoint width and the numerical vertex bound. -/
def steinerBinaryToUnaryMachine_endpoint (word : List Bool) {n : ℕ}
    (valid : binaryWordValue word < n) :
    TM2OutputsInTime steinerBinaryToUnaryMachine word
      (some (encodeSteinerUnaryProductCount ((⟨binaryWordValue word,valid⟩ : Fin n).val))) (4*word.length+3*n+2) :=
  let run := steinerBinaryToUnaryMachine_value_time word
  ⟨run.toEvalsTo,run.steps_le_m.trans (by omega)⟩

/-- A successful range flag is sufficient to use the endpoint bound
when the supplied raw bound represents the graph's vertex count. -/
def steinerBinaryToUnaryMachine_checkedEndpoint {n : ℕ} (word bound : List Bool)
    (boundValue : binaryWordValue bound = n)
    (accepted : steinerRangeChecks [(word,bound)] = true) :
    TM2OutputsInTime steinerBinaryToUnaryMachine word
      (some (encodeSteinerUnaryProductCount (binaryWordValue word))) (4*word.length+3*n+2) := by
  have checked : (binaryLessWithWork word bound false).1 = true := by simpa [steinerRangeChecks] using accepted
  have valid : binaryWordValue word < n := by
    rw [← boundValue]
    rw [(binaryLessWithWork_noBorrow_spec word bound).1] at checked
    exact of_decide_eq_true checked
  exact steinerBinaryToUnaryMachine_endpoint word valid

end OnlineReachabilityPreservers
