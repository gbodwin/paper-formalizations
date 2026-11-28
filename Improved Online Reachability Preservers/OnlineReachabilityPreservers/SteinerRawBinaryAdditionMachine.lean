import OnlineReachabilityPreservers.SteinerBinaryAdditionMachine
import OnlineReachabilityPreservers.SteinerBinaryAlignmentMachine
import OnlineReachabilityPreservers.SteinerStackFrame
import OnlineReachabilityPreservers.SteinerStackReturn

/-! Compose the verified binary alignment and addition machines on separately framed words. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private inductive RawAdditionLabel where
  | start
  | align (carry : Bool) (label : Fin 4)
  | addStart (carry : Bool)
  | add (label : Fin 3)
  deriving Fintype

private abbrev WordAlignmentRegister := steinerBinaryAlignmentMachine.σ
private abbrev PairAdderRegister := steinerBinaryAdditionMachine.σ
private abbrev RawAdditionRegister := Option SteinerAlignmentSymbol × WordAlignmentRegister × PairAdderRegister
private abbrev RawAdditionProgram :=
  Turing.TM2.Stmt (fun _ : Fin 3 => SteinerAlignmentSymbol) RawAdditionLabel RawAdditionRegister

private def rawAdditionInitial : RawAdditionRegister :=
  (none,steinerBinaryAlignmentMachine.initialState,steinerBinaryAdditionMachine.initialState)

private def rawAlignmentTag (carry : Bool) :
    StackMachineTag SteinerAlignmentSymbol SteinerAlignmentSymbol (Fin 4) RawAdditionLabel
      WordAlignmentRegister RawAdditionRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (none,r,steinerBinaryAdditionMachine.initialState)
  readRegister r := r.2.1
  writeLabel := RawAdditionLabel.align carry
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def rawAdderTapes : Bool ↪ Fin 3 where
  toFun
    | false => 0
    | true => 1
  inj' := by intro a b same; cases a <;> cases b <;> first | rfl | contradiction

private def rawAdderTag :
    StackMachineTag (Bool × Bool) SteinerAlignmentSymbol (Fin 3) RawAdditionLabel
      PairAdderRegister RawAdditionRegister where
  writeSymbol := Sum.inr
  readSymbol
    | .inl _ => none
    | .inr pair => some pair
  writeRegister r := (none,steinerBinaryAlignmentMachine.initialState,r)
  readRegister r := r.2.2
  writeLabel := RawAdditionLabel.add
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def rawAdderFramedProgram (label : Fin 3) :
    StackMachineTag.Program (Fin 3) (Bool × Bool) (Fin 3) PairAdderRegister :=
  StackIndexEmbedding.statement rawAdderTapes (steinerBinaryAdditionMachine.m label)

private def rawCarry : Option SteinerAlignmentSymbol → Bool
  | some (.inl (some carry)) => carry
  | _ => false

private def rawAdditionProgram : RawAdditionLabel → RawAdditionProgram
  | .start =>
    pop 0 (fun r observed => (observed,r.2)) <|
      branch (fun r => rawCarry r.1)
        (load (fun _ => rawAdditionInitial) <| goto fun _ => .align true 0)
        (load (fun _ => rawAdditionInitial) <| goto fun _ => .align false 0)
  | .align carry label =>
    (rawAlignmentTag carry).returningStatement (.addStart carry) (steinerBinaryAlignmentMachine.m label)
  | .addStart carry => push 0 (fun _ => Sum.inr (carry,false)) <| goto fun _ => .add 0
  | .add label => rawAdderTag.statement (rawAdderFramedProgram label)

/-- Read the carry, align the two separately supplied words, and run the
existing packed-pair adder on the resulting digit pairs. -/
abbrev steinerRawBinaryAdditionMachine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 0
  Γ _ := SteinerAlignmentSymbol
  Λ := RawAdditionLabel
  main := .start
  σ := RawAdditionRegister
  initialState := rawAdditionInitial
  m := rawAdditionProgram

/-- A single carry bit precedes the two divider-framed binary words. -/
def encodeSteinerRawBinaryAddition (request : List Bool × List Bool × Bool) : List SteinerAlignmentSymbol :=
  Sum.inl (some request.2.2)::encodeSteinerAlignmentOperands (request.1,request.2.1)

def encodeSteinerRawBinarySum (sum : List Bool) : List SteinerAlignmentSymbol :=
  (encodeSteinerBinarySum sum).map Sum.inr

private def rawAdditionCfg (label : Option RawAdditionLabel) (tape : List SteinerAlignmentSymbol) :
    steinerRawBinaryAdditionMachine.Cfg where
  l := label
  var := rawAdditionInitial
  stk := ![tape,[],[]]

private theorem rawAddition_update (tape next : List SteinerAlignmentSymbol) :
    Function.update (![tape,[],[]] : Fin 3 → List SteinerAlignmentSymbol) 0 next =
      ![next,[],[]] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem rawAddition_start (carry : Bool) (tape : List SteinerAlignmentSymbol) :
    steinerRawBinaryAdditionMachine.step (rawAdditionCfg (some .start) (Sum.inl (some carry)::tape)) =
      some (rawAdditionCfg (some (.align carry 0)) tape) := by
  cases carry <;>
    simp [FinTM2.step,steinerRawBinaryAdditionMachine,rawAdditionCfg,Turing.TM2.step,
      Turing.TM2.stepAux,rawAdditionProgram,rawCarry,rawAddition_update] <;> rfl

private theorem rawAddition_addStart (carry : Bool) (tape : List SteinerAlignmentSymbol) :
    steinerRawBinaryAdditionMachine.step (rawAdditionCfg (some (.addStart carry)) tape) =
      some (rawAdditionCfg (some (.add 0)) (Sum.inr (carry,false)::tape)) := by
  simp [FinTM2.step,steinerRawBinaryAdditionMachine,rawAdditionCfg,Turing.TM2.step,
    Turing.TM2.stepAux,rawAdditionProgram,rawAddition_update]
  rfl

private def rawAdditionOne {a b : steinerRawBinaryAdditionMachine.Cfg}
    (step : steinerRawBinaryAdditionMachine.step a = some b) :
    EvalsToInTime steinerRawBinaryAdditionMachine.step a (some b) 1 where
  steps := 1
  evals_in_steps := by change steinerRawBinaryAdditionMachine.step a = some b; exact step
  steps_le_m := le_rfl

private theorem rawAddition_init (tape : List SteinerAlignmentSymbol) :
    initList steinerRawBinaryAdditionMachine tape = rawAdditionCfg (some .start) tape := by
  unfold initList rawAdditionCfg
  apply congrArg (fun stk : Fin 3 → List SteinerAlignmentSymbol =>
    (⟨some RawAdditionLabel.start,rawAdditionInitial,stk⟩ : steinerRawBinaryAdditionMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem rawAddition_halt (tape : List SteinerAlignmentSymbol) :
    haltList steinerRawBinaryAdditionMachine tape = rawAdditionCfg none tape := by
  unfold haltList rawAdditionCfg
  apply congrArg (fun stk : Fin 3 → List SteinerAlignmentSymbol =>
    (⟨none,rawAdditionInitial,stk⟩ : steinerRawBinaryAdditionMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem rawAlignment_init (carry : Bool) (tape : List SteinerAlignmentSymbol) :
    (rawAlignmentTag carry).returningConfiguration (.addStart carry) (initList steinerBinaryAlignmentMachine tape) =
      rawAdditionCfg (some (.align carry 0)) tape := by
  apply congrArg (fun stk : Fin 3 → List SteinerAlignmentSymbol =>
    (⟨some (RawAdditionLabel.align carry 0),rawAdditionInitial,stk⟩ : steinerRawBinaryAdditionMachine.Cfg))
  funext i
  fin_cases i
  · change tape.map id = tape
    simp
  all_goals rfl

private theorem rawAlignment_return (carry : Bool) (out : List SteinerAlignmentSymbol) :
    (rawAlignmentTag carry).returningConfiguration (.addStart carry) (haltList steinerBinaryAlignmentMachine out) =
      rawAdditionCfg (some (.addStart carry)) out := by
  apply congrArg (fun stk : Fin 3 → List SteinerAlignmentSymbol =>
    (⟨some (RawAdditionLabel.addStart carry),rawAdditionInitial,stk⟩ : steinerRawBinaryAdditionMachine.Cfg))
  funext i
  fin_cases i
  · change out.map id = out
    simp
  all_goals rfl

private theorem rawAdder_init (tape : List (Bool × Bool)) :
    rawAdderTag.configuration (StackIndexEmbedding.configuration rawAdderTapes (fun _ => [])
      (initList steinerBinaryAdditionMachine tape)) =
      rawAdditionCfg (some (.add 0)) (tape.map Sum.inr) := by
  apply congrArg (fun stk : Fin 3 → List SteinerAlignmentSymbol =>
    (⟨some (RawAdditionLabel.add 0),rawAdditionInitial,stk⟩ : steinerRawBinaryAdditionMachine.Cfg))
  funext i
  fin_cases i
  · change (StackIndexEmbedding.tapesAt rawAdderTapes (initList steinerBinaryAdditionMachine tape).stk
      (fun _ => []) (rawAdderTapes false)).map Sum.inr = tape.map Sum.inr
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change (StackIndexEmbedding.tapesAt rawAdderTapes (initList steinerBinaryAdditionMachine tape).stk
      (fun _ => []) (rawAdderTapes true)).map Sum.inr = []
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change (StackIndexEmbedding.tapesAt rawAdderTapes (initList steinerBinaryAdditionMachine tape).stk
      (fun _ => []) 2).map Sum.inr = []
    rw [StackIndexEmbedding.tapesAt_extra rawAdderTapes _ _ (by intro k; cases k <;> decide)]
    rfl

private theorem rawAdder_halt (out : List (Bool × Bool)) :
    rawAdderTag.configuration (StackIndexEmbedding.configuration rawAdderTapes (fun _ => [])
      (haltList steinerBinaryAdditionMachine out)) =
      rawAdditionCfg none (out.map Sum.inr) := by
  apply congrArg (fun stk : Fin 3 → List SteinerAlignmentSymbol =>
    (⟨none,rawAdditionInitial,stk⟩ : steinerRawBinaryAdditionMachine.Cfg))
  funext i
  fin_cases i
  · change (StackIndexEmbedding.tapesAt rawAdderTapes (haltList steinerBinaryAdditionMachine out).stk
      (fun _ => []) (rawAdderTapes false)).map Sum.inr = out.map Sum.inr
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change (StackIndexEmbedding.tapesAt rawAdderTapes (haltList steinerBinaryAdditionMachine out).stk
      (fun _ => []) (rawAdderTapes true)).map Sum.inr = []
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change (StackIndexEmbedding.tapesAt rawAdderTapes (haltList steinerBinaryAdditionMachine out).stk
      (fun _ => []) 2).map Sum.inr = []
    rw [StackIndexEmbedding.tapesAt_extra rawAdderTapes _ _ (by intro k; cases k <;> decide)]
    rfl

private def rawAlignmentEval (carry : Bool) (words : List Bool × List Bool) :
    EvalsToInTime steinerRawBinaryAdditionMachine.step
      (rawAdditionCfg (some (.align carry 0)) (encodeSteinerAlignmentOperands words))
      (some (rawAdditionCfg (some (.addStart carry))
        (encodeSteinerAlignedDigits (steinerBinaryAlignmentAnswer words))))
      (2*words.1.length+2*(steinerBinaryAlignmentAnswer words).length+4) := by
  have moved := (rawAlignmentTag carry).evaluationReturning (.addStart carry)
    (base := steinerBinaryAlignmentMachine.m) (host := rawAdditionProgram)
    (fun _ => rfl) (steinerBinaryAlignmentMachine_run words)
  change EvalsToInTime steinerRawBinaryAdditionMachine.step
    ((rawAlignmentTag carry).returningConfiguration (.addStart carry)
      (initList steinerBinaryAlignmentMachine (encodeSteinerAlignmentOperands words)))
    (some ((rawAlignmentTag carry).returningConfiguration (.addStart carry)
      (haltList steinerBinaryAlignmentMachine (encodeSteinerAlignedDigits (steinerBinaryAlignmentAnswer words))))) _ at moved
  rw [rawAlignment_init,rawAlignment_return] at moved
  exact moved

private def rawAdderEval (request : List Bool × List Bool × Bool) :
    EvalsToInTime steinerRawBinaryAdditionMachine.step
      (rawAdditionCfg (some (.add 0)) ((encodeSteinerBinaryAddition request).map Sum.inr))
      (some (rawAdditionCfg none (encodeSteinerRawBinarySum (steinerBinaryAdditionAnswer request))))
      (2*(encodeSteinerBinaryAddition request).length+2) := by
  let count := steinerBinaryAdditionMachine_run request
  refine ⟨⟨count.steps,?_⟩,count.steps_le_m⟩
  let frame := StackIndexEmbedding.evaluation rawAdderTapes (base := steinerBinaryAdditionMachine.m)
    (fun _ => []) count
  let tagged := rawAdderTag.evaluation (base := rawAdderFramedProgram) (host := rawAdditionProgram) (fun _ => rfl) frame
  have executed : (flip bind steinerRawBinaryAdditionMachine.step)^[count.steps]
      (some (rawAdderTag.configuration (StackIndexEmbedding.configuration rawAdderTapes (fun _ => [])
        (initList steinerBinaryAdditionMachine (encodeSteinerBinaryAddition request))))) =
      some (rawAdderTag.configuration (StackIndexEmbedding.configuration rawAdderTapes (fun _ => [])
        (haltList steinerBinaryAdditionMachine (encodeSteinerBinarySum (steinerBinaryAdditionAnswer request))))) :=
    tagged.evals_in_steps
  rw [rawAdder_init,rawAdder_halt] at executed
  exact executed

/-- For actual separately framed operands, the machine returns the
existing adder's exact sum word within a linear transition bound. -/
def steinerRawBinaryAdditionMachine_run (request : List Bool × List Bool × Bool) :
    TM2OutputsInTime steinerRawBinaryAdditionMachine (encodeSteinerRawBinaryAddition request)
      (some (encodeSteinerRawBinarySum (steinerBinaryAdditionAnswer request)))
      (2*request.1.length+4*(max request.1.length request.2.1.length)+10) := by
  rcases request with ⟨left,right,carry⟩
  let digits := alignBinaryDigits left right
  let tape := encodeSteinerAlignmentOperands (left,right)
  let pairs := encodeSteinerAlignedDigits digits
  have first := rawAdditionOne (rawAddition_start carry tape)
  have aligned := rawAlignmentEval carry (left,right)
  have addStart := rawAdditionOne (rawAddition_addStart carry pairs)
  have sum := rawAdderEval (left,right,carry)
  have scanned := EvalsToInTime.trans _ _ _ _ _ _ first aligned
  have ready := EvalsToInTime.trans _ _ _ _ _ _ scanned addStart
  have all := EvalsToInTime.trans _ _ _ _ _ _ ready sum
  have digitLength : digits.length = max left.length right.length := steinerBinaryAlignmentAnswer_length (left,right)
  have pairLength : (encodeSteinerBinaryAddition (left,right,carry)).length = digits.length+1 := rfl
  change EvalsToInTime steinerRawBinaryAdditionMachine.step _ (some (haltList steinerRawBinaryAdditionMachine _)) _
  rw [rawAddition_init,rawAddition_halt]
  refine ⟨all.toEvalsTo,?_⟩
  have paid := all.steps_le_m
  change all.steps ≤ 2*(encodeSteinerBinaryAddition (left,right,carry)).length+2+
    (1+(2*left.length+2*digits.length+4+1)) at paid
  change all.steps ≤ 2*left.length+4*(max left.length right.length)+10
  omega

/-- The raw-input adder is polynomial-time in the two word lengths, the
carry header, and the divider. -/
noncomputable def steinerRawBinaryAdditionMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerRawBinaryAddition encodeSteinerRawBinarySum steinerBinaryAdditionAnswer where
  tm := steinerRawBinaryAdditionMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 6*Polynomial.X
  outputsFun request := by
    have run := steinerRawBinaryAdditionMachine_run request
    have width : (encodeSteinerRawBinaryAddition request).length = request.1.length+request.2.1.length+2 := by
      simp only [encodeSteinerRawBinaryAddition,encodeSteinerAlignmentOperands,encodeSteinerAlignmentWord,
        List.length_cons,List.length_append,List.length_map]
      omega
    have paid : 2*request.1.length+4*(max request.1.length request.2.1.length)+10 ≤
        (Polynomial.C 6*Polynomial.X).eval (encodeSteinerRawBinaryAddition request).length := by
      simp only [Polynomial.eval_C_mul,Polynomial.eval_X,width]
      omega
    change TM2OutputsInTime steinerRawBinaryAdditionMachine ((encodeSteinerRawBinaryAddition request).map id)
      (some ((encodeSteinerRawBinarySum (steinerBinaryAdditionAnswer request)).map id)) _
    simpa only [List.map_id_fun,id_eq] using
      (show TM2OutputsInTime steinerRawBinaryAdditionMachine (encodeSteinerRawBinaryAddition request)
        (some (encodeSteinerRawBinarySum (steinerBinaryAdditionAnswer request))) _ from
          ⟨run.toEvalsTo,run.steps_le_m.trans paid⟩)

end OnlineReachabilityPreservers
