import OnlineReachabilityPreservers.SteinerDistanceHopTransferRows
import OnlineReachabilityPreservers.SteinerUnaryHopMinimumRowFrameMachine

/-! Evaluate a relaxation row directly from the prepared transfer cells. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing

private abbrev HopMinRowSymbol := SteinerUnaryCappedRowsSymbol
private abbrev HopMinPrepLabel := steinerUnaryHopMinimumRowFrameMachine.Λ
private abbrev HopMinPrepRegister := steinerUnaryHopMinimumRowFrameMachine.σ
private abbrev HopMinLabel := steinerUnaryMinimumMachine.Λ
private abbrev HopMinRegister := steinerUnaryMinimumMachine.σ
private instance : Fintype HopMinPrepLabel := steinerUnaryHopMinimumRowFrameMachine.ΛFin
private instance : Fintype HopMinLabel := steinerUnaryMinimumMachine.ΛFin

private inductive HopMinRowLabel where
  | prepare (label : HopMinPrepLabel)
  | minimum (label : HopMinLabel)
  deriving Fintype

private abbrev HopMinRowRegister := HopMinPrepRegister × HopMinRegister
private abbrev HopMinRowProgram := StackMachineTag.Program (Fin 6) HopMinRowSymbol HopMinRowLabel HopMinRowRegister

private def hopMinRowInitial : HopMinRowRegister :=
  (steinerUnaryHopMinimumRowFrameMachine.initialState,steinerUnaryMinimumMachine.initialState)

private def hopMinPrepTag :
    StackMachineTag HopMinRowSymbol HopMinRowSymbol HopMinPrepLabel HopMinRowLabel HopMinPrepRegister HopMinRowRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (r,steinerUnaryMinimumMachine.initialState)
  readRegister := Prod.fst
  writeLabel := .prepare
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def hopMinTag :
    StackMachineTag HopMinRowSymbol HopMinRowSymbol HopMinLabel HopMinRowLabel HopMinRegister HopMinRowRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (steinerUnaryHopMinimumRowFrameMachine.initialState,r)
  readRegister := Prod.snd
  writeLabel := .minimum
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def hopMinStart : HopMinRowLabel := .minimum steinerUnaryMinimumMachine.main

private def hopMinSlots : Fin 4 ↪ Fin 6 where
  toFun i := ⟨i.val,i.isLt.trans (by decide)⟩
  inj' := fun _ _ eq => Fin.ext (congrArg (Fin.val : Fin 6 → ℕ) eq)

private def hopMinCode : HopMinRowLabel → StackMachineTag.Program (Fin 4) HopMinRowSymbol HopMinRowLabel HopMinRowRegister
  | .minimum label => hopMinTag.statement (steinerUnaryMinimumMachine.m label)
  | .prepare _ => Turing.TM2.Stmt.halt

private def hopMinRowProgram : HopMinRowLabel → HopMinRowProgram
  | .prepare label => hopMinPrepTag.returningStatement hopMinStart (steinerUnaryHopMinimumRowFrameMachine.m label)
  | .minimum label => StackIndexEmbedding.statement hopMinSlots (hopMinCode (.minimum label))

/-- Evaluate the transfer cells and run unary minimization directly
on the prepared input stack. -/
abbrev steinerUnaryHopMinimumRowMachine : FinTM2 where
  K := Fin 6
  k₀ := 3
  k₁ := 3
  Γ _ := HopMinRowSymbol
  Λ := HopMinRowLabel
  main := .prepare steinerUnaryHopMinimumRowFrameMachine.main
  σ := HopMinRowRegister
  initialState := hopMinRowInitial
  m := hopMinRowProgram

private def hopMinRowReady (word : List HopMinRowSymbol) : steinerUnaryHopMinimumRowMachine.Cfg :=
  ⟨some hopMinStart,hopMinRowInitial,![word,[],[],[],[],[]]⟩

private theorem hopMinPrep_init (word : List HopMinRowSymbol) :
    hopMinPrepTag.returningConfiguration hopMinStart (initList steinerUnaryHopMinimumRowFrameMachine word) =
      initList steinerUnaryHopMinimumRowMachine word := by
  apply congrArg (fun tapes : Fin 6 → List HopMinRowSymbol =>
    (⟨some (.prepare steinerUnaryHopMinimumRowFrameMachine.main),hopMinRowInitial,tapes⟩ : steinerUnaryHopMinimumRowMachine.Cfg))
  funext i
  change ((initList steinerUnaryHopMinimumRowFrameMachine word).stk i).map id = _
  rw [List.map_id]
  rfl

private theorem hopMinPrep_return (word : List HopMinRowSymbol) :
    hopMinPrepTag.returningConfiguration hopMinStart (haltList steinerUnaryHopMinimumRowFrameMachine word) =
      hopMinRowReady word := by
  apply congrArg (fun tapes : Fin 6 → List HopMinRowSymbol =>
    (⟨some hopMinStart,hopMinRowInitial,tapes⟩ : steinerUnaryHopMinimumRowMachine.Cfg))
  funext i
  change ((haltList steinerUnaryHopMinimumRowFrameMachine word).stk i).map id = _
  rw [List.map_id]
  fin_cases i <;> rfl

private noncomputable def hopMinHosted (c : steinerUnaryMinimumMachine.Cfg) : steinerUnaryHopMinimumRowMachine.Cfg :=
  StackIndexEmbedding.configuration hopMinSlots (fun _ => []) (hopMinTag.configuration c)

private theorem hopMin_step {c after : steinerUnaryMinimumMachine.Cfg} (move : steinerUnaryMinimumMachine.step c = some after) :
    steinerUnaryHopMinimumRowMachine.step (hopMinHosted c) = some (hopMinHosted after) := by
  have tagged := hopMinTag.step_embedded (base := steinerUnaryMinimumMachine.m) (host := hopMinCode) (fun _ => rfl) c
  change Turing.TM2.step steinerUnaryMinimumMachine.m c = some after at move
  rw [move] at tagged
  have hosted := StackIndexEmbedding.step_on hopMinSlots (base := hopMinCode) (fun _ => []) (hopMinTag.configuration c)
  rw [tagged] at hosted
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact hosted

private theorem hopMin_tapes (c : steinerUnaryMinimumMachine.Cfg) (input out : List HopMinRowSymbol)
    (shape : c.stk = ![input,[],[],out]) : (hopMinHosted c).stk = ![input,[],[],out,[],[]] := by
  have image (i : Fin 4) : (hopMinHosted c).stk (hopMinSlots i) = (![input,[],[],out] : Fin 4 → List HopMinRowSymbol) i := by
    change StackIndexEmbedding.tapesAt hopMinSlots (fun k => (c.stk k).map id) (fun _ => []) (hopMinSlots i) = _
    rw [StackIndexEmbedding.tapesAt_image,List.map_id,shape]
  have other (i : Fin 6) (absent : ∀ j, hopMinSlots j ≠ i) : (hopMinHosted c).stk i = [] := by
    change StackIndexEmbedding.tapesAt hopMinSlots (fun k => (c.stk k).map id) (fun _ => []) i = []
    exact StackIndexEmbedding.tapesAt_extra hopMinSlots _ _ absent
  funext i
  fin_cases i
  · exact image 0
  · exact image 1
  · exact image 2
  · exact image 3
  · exact other 4 (by intro j; fin_cases j <;> decide)
  · exact other 5 (by intro j; fin_cases j <;> decide)

private theorem hopMin_init (word : List HopMinRowSymbol) :
    hopMinHosted (initList steinerUnaryMinimumMachine word) = hopMinRowReady word := by
  apply congrArg (fun tapes : Fin 6 → List HopMinRowSymbol =>
    (⟨some hopMinStart,hopMinRowInitial,tapes⟩ : steinerUnaryHopMinimumRowMachine.Cfg))
  apply hopMin_tapes
  funext i
  fin_cases i <;> rfl

private theorem hopMin_halt (word : List HopMinRowSymbol) :
    hopMinHosted (haltList steinerUnaryMinimumMachine word) = haltList steinerUnaryHopMinimumRowMachine word := by
  apply congrArg (fun tapes : Fin 6 → List HopMinRowSymbol =>
    (⟨none,hopMinRowInitial,tapes⟩ : steinerUnaryHopMinimumRowMachine.Cfg))
  have tapes := hopMin_tapes (haltList steinerUnaryMinimumMachine word) [] word (by funext i; fin_cases i <;> rfl)
  refine tapes.trans ?_
  funext i
  fin_cases i <;> rfl

/-- The minimum of the cap and the values of the supplied transfer cells. -/
def steinerUnaryHopMinimumRowValue (request : ℕ × List (ℕ × ℕ)) : ℕ :=
  (request.2.map fun (code,prior) => if code ≤ 1 then prior+code else request.1).foldl min request.1

/-- The complete row evaluates in linear native time in its supplied
expanded input frame. -/
noncomputable def steinerUnaryHopMinimumRowMachine_run (request : ℕ × List (ℕ × ℕ)) :
    let input := encodeSteinerUnaryHopMinimumRowFrame request
    TM2OutputsInTime steinerUnaryHopMinimumRowMachine input
      (some (encodeSteinerUnaryRoundTotal (steinerUnaryHopMinimumRowValue request))) (8*input.length+3) := by
  let input := encodeSteinerUnaryHopMinimumRowFrame request
  let values := request.2.map fun cell => if cell.1 ≤ 1 then cell.2+cell.1 else request.1
  let frame := encodeSteinerUnaryMinimum (request.1,values)
  let result := encodeSteinerUnaryRoundTotal (steinerUnaryHopMinimumRowValue request)
  have first := hopMinPrepTag.evaluationReturning hopMinStart (base := steinerUnaryHopMinimumRowFrameMachine.m)
    (host := hopMinRowProgram) (fun _ => rfl) (steinerUnaryHopMinimumRowFrameMachine_run request)
  rw [hopMinPrep_init,hopMinPrep_return] at first
  let minEval := steinerUnaryMinimumMachine_run (request.1,values)
  have hosted := iterate_map_some hopMinHosted (fun move => hopMin_step move) minEval.steps minEval.evals_in_steps
  rw [hopMin_init,hopMin_halt] at hosted
  have second : EvalsToInTime steinerUnaryHopMinimumRowMachine.step (hopMinRowReady frame)
      (some (haltList steinerUnaryHopMinimumRowMachine result)) (2*frame.length+1) :=
    ⟨⟨minEval.steps,hosted⟩,minEval.steps_le_m⟩
  have both := EvalsToInTime.trans _ _ _ _ _ _ first second
  have size : frame.length ≤ input.length := steinerUnaryHopMinimumRowFrameAnswer_length_le request
  refine ⟨both.toEvalsTo,both.steps_le_m.trans ?_⟩
  change (2*frame.length+1)+(6*input.length+2) ≤ 8*input.length+3
  omega

/-- Native row minimization has a linear transition polynomial. -/
noncomputable def steinerUnaryHopMinimumRowMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryHopMinimumRowFrame encodeSteinerUnaryRoundTotal steinerUnaryHopMinimumRowValue where
  tm := steinerUnaryHopMinimumRowMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 8*Polynomial.X+Polynomial.C 3
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_C,
      Polynomial.eval_X] using steinerUnaryHopMinimumRowMachine_run request

/-- A single source row uses the preceding column at the fixed target. -/
def steinerUnaryHopMinimumSourceRow {n : ℕ} (G : Arcs (Fin n)) (depth : ℕ) (source target : Fin n) :
    ℕ × List (ℕ × ℕ) :=
  (n+1,List.ofFn fun next => (steinerHopTransferCode G (source,next),steinerDistanceHopRounds G depth (next,target)))

/-- The actual native row run returns the next hop entry from the
supplied encoded source row and previous column values. -/
noncomputable def steinerUnaryHopMinimumRowMachine_hopRound {n : ℕ} (G : Arcs (Fin n)) (depth : ℕ) (source target : Fin n) :
    let input := encodeSteinerUnaryHopMinimumRowFrame (steinerUnaryHopMinimumSourceRow G depth source target)
    TM2OutputsInTime steinerUnaryHopMinimumRowMachine input
      (some (encodeSteinerUnaryRoundTotal (steinerDistanceHopRounds G (depth+1) (source,target)))) (8*input.length+3) := by
  have col := steinerHopTransferRound_eq_hopRounds G depth target
  have entry := congrArg (fun v : Vector ℕ n => v[source.val]) col
  simp only [steinerHopTransferRound,Vector.getElem_ofFn] at entry
  have exactValue : steinerUnaryHopMinimumRowValue (steinerUnaryHopMinimumSourceRow G depth source target) =
      steinerDistanceHopRounds G (depth+1) (source,target) := by
    simp only [steinerUnaryHopMinimumRowValue,steinerUnaryHopMinimumSourceRow,List.map_ofFn,Function.comp_def]
    exact entry
  simpa only [exactValue] using steinerUnaryHopMinimumRowMachine_run (steinerUnaryHopMinimumSourceRow G depth source target)

end OnlineReachabilityPreservers
