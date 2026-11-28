import OnlineReachabilityPreservers.SteinerUnaryDistanceRoundFrameMachine

/-! Run a round from the distance rows and one stored vector of earlier weights. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing

private abbrev DistanceRoundPrepLabel := steinerUnaryDistanceRoundFrameMachine.Λ
private abbrev DistanceRoundPrepRegister := steinerUnaryDistanceRoundFrameMachine.σ
private abbrev DistanceRoundSumLabel := steinerUnarySharedCapRowsMachine.Λ
private abbrev DistanceRoundSumRegister := steinerUnarySharedCapRowsMachine.σ
private instance : Fintype DistanceRoundPrepLabel := steinerUnaryDistanceRoundFrameMachine.ΛFin
private instance : Fintype DistanceRoundSumLabel := steinerUnarySharedCapRowsMachine.ΛFin

private inductive DistanceRoundLabel where
  | prepare (label : DistanceRoundPrepLabel)
  | sum (label : DistanceRoundSumLabel)
  deriving Fintype

private abbrev DistanceRoundSymbol := SteinerUnaryCappedRowsSymbol
private abbrev DistanceRoundRegister := DistanceRoundPrepRegister × DistanceRoundSumRegister
private abbrev DistanceRoundProgram :=
  StackMachineTag.Program (Fin 7) DistanceRoundSymbol DistanceRoundLabel DistanceRoundRegister

private def distanceRoundInitial : DistanceRoundRegister :=
  (steinerUnaryDistanceRoundFrameMachine.initialState,steinerUnarySharedCapRowsMachine.initialState)

private def distanceRoundPrepTag :
    StackMachineTag DistanceRoundSymbol DistanceRoundSymbol DistanceRoundPrepLabel DistanceRoundLabel
      DistanceRoundPrepRegister DistanceRoundRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (r,steinerUnarySharedCapRowsMachine.initialState)
  readRegister := Prod.fst
  writeLabel := .prepare
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def distanceRoundSumTag :
    StackMachineTag DistanceRoundSymbol DistanceRoundSymbol DistanceRoundSumLabel DistanceRoundLabel
      DistanceRoundSumRegister DistanceRoundRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (steinerUnaryDistanceRoundFrameMachine.initialState,r)
  readRegister := Prod.snd
  writeLabel := .sum
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def distanceRoundReturn : DistanceRoundLabel := .sum steinerUnarySharedCapRowsMachine.main

/-- The frame adapter writes onto the shared-cap machine's input stack. -/
private def distanceRoundPrepSlots : Fin 4 ↪ Fin 7 where
  toFun := ![0,4,5,6]
  inj' := by
    intro a b same
    fin_cases a <;> fin_cases b <;> simp_all

private def distanceRoundInner :
    DistanceRoundLabel → StackMachineTag.Program (Fin 4) DistanceRoundSymbol DistanceRoundLabel DistanceRoundRegister
  | .prepare label => distanceRoundPrepTag.returningStatement distanceRoundReturn
      (steinerUnaryDistanceRoundFrameMachine.m label)
  | .sum _ => Turing.TM2.Stmt.halt

private def distanceRoundProgram : DistanceRoundLabel → DistanceRoundProgram
  | .prepare label => StackIndexEmbedding.statement distanceRoundPrepSlots (distanceRoundInner (.prepare label))
  | .sum label => distanceRoundSumTag.statement (steinerUnarySharedCapRowsMachine.m label)

/-- Form the shared-cap pair frame and evaluate it on the same tapes,
without a transfer between the two phases. -/
abbrev steinerUnaryDistanceRoundMachine : FinTM2 where
  K := Fin 7
  k₀ := 5
  k₁ := 5
  Γ _ := DistanceRoundSymbol
  Λ := DistanceRoundLabel
  main := .prepare steinerUnaryDistanceRoundFrameMachine.main
  σ := DistanceRoundRegister
  initialState := distanceRoundInitial
  m := distanceRoundProgram

private def distanceRoundCfg (label : Option DistanceRoundLabel) (word : List DistanceRoundSymbol) :
    steinerUnaryDistanceRoundMachine.Cfg where
  l := label
  var := distanceRoundInitial
  stk := ![[],[],[],[],[],word,[]]

private noncomputable def distanceRoundPrepared (c : steinerUnaryDistanceRoundFrameMachine.Cfg) :
    steinerUnaryDistanceRoundMachine.Cfg :=
  StackIndexEmbedding.configuration distanceRoundPrepSlots (fun _ => [])
    (distanceRoundPrepTag.returningConfiguration distanceRoundReturn c)

private theorem distanceRound_prepStep {c after : steinerUnaryDistanceRoundFrameMachine.Cfg}
    (move : steinerUnaryDistanceRoundFrameMachine.step c = some after) :
    steinerUnaryDistanceRoundMachine.step (distanceRoundPrepared c) = some (distanceRoundPrepared after) := by
  have tagged := distanceRoundPrepTag.step_embedded_return distanceRoundReturn
    (base := steinerUnaryDistanceRoundFrameMachine.m) (host := distanceRoundInner) (fun _ => rfl) move
  have framed := StackIndexEmbedding.step_on distanceRoundPrepSlots (base := distanceRoundInner)
    (fun _ => []) (distanceRoundPrepTag.returningConfiguration distanceRoundReturn c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem distanceRound_prepTapes (word : List DistanceRoundSymbol) (c : steinerUnaryDistanceRoundFrameMachine.Cfg)
    (tapes : c.stk = ![[],[],word,[]]) :
    (distanceRoundPrepared c).stk = ![[],[],[],[],[],word,[]] := by
  have image (i : Fin 4) : (distanceRoundPrepared c).stk (distanceRoundPrepSlots i) =
      (![[],[],word,[]] : Fin 4 → List DistanceRoundSymbol) i := by
    change StackIndexEmbedding.tapesAt distanceRoundPrepSlots (fun k => (c.stk k).map id) (fun _ => [])
      (distanceRoundPrepSlots i) = _
    rw [StackIndexEmbedding.tapesAt_image,List.map_id,tapes]
  have extra (i : Fin 7) (absent : ∀ j, distanceRoundPrepSlots j ≠ i) :
      (distanceRoundPrepared c).stk i = [] := by
    change StackIndexEmbedding.tapesAt distanceRoundPrepSlots (fun k => (c.stk k).map id) (fun _ => []) i = []
    exact StackIndexEmbedding.tapesAt_extra distanceRoundPrepSlots _ _ absent
  funext i
  fin_cases i
  · exact image 0
  · exact extra 1 (by intro j; fin_cases j <;> decide)
  · exact extra 2 (by intro j; fin_cases j <;> decide)
  · exact extra 3 (by intro j; fin_cases j <;> decide)
  · exact image 1
  · exact image 2
  · exact image 3

private theorem distanceRound_prepInit (word : List DistanceRoundSymbol) :
    distanceRoundPrepared (initList steinerUnaryDistanceRoundFrameMachine word) =
      initList steinerUnaryDistanceRoundMachine word := by
  have lifted := distanceRound_prepTapes word (initList steinerUnaryDistanceRoundFrameMachine word)
    (by funext i; fin_cases i <;> rfl)
  apply congrArg (fun stk : Fin 7 → List DistanceRoundSymbol =>
    (⟨some (.prepare steinerUnaryDistanceRoundFrameMachine.main),distanceRoundInitial,stk⟩ :
      steinerUnaryDistanceRoundMachine.Cfg))
  refine lifted.trans ?_
  funext i
  fin_cases i <;> rfl

private theorem distanceRound_prepReturn (word : List DistanceRoundSymbol) :
    distanceRoundPrepared (haltList steinerUnaryDistanceRoundFrameMachine word) =
      distanceRoundCfg (some distanceRoundReturn) word := by
  apply congrArg (fun stk : Fin 7 → List DistanceRoundSymbol =>
    (⟨some distanceRoundReturn,distanceRoundInitial,stk⟩ : steinerUnaryDistanceRoundMachine.Cfg))
  apply distanceRound_prepTapes
  funext i
  fin_cases i <;> rfl

private theorem distanceRound_sumInit (word : List DistanceRoundSymbol) :
    distanceRoundSumTag.configuration (initList steinerUnarySharedCapRowsMachine word) =
      distanceRoundCfg (some distanceRoundReturn) word := by
  apply congrArg (fun stk : Fin 7 → List DistanceRoundSymbol =>
    (⟨some distanceRoundReturn,distanceRoundInitial,stk⟩ : steinerUnaryDistanceRoundMachine.Cfg))
  funext i
  change ((initList steinerUnarySharedCapRowsMachine word).stk i).map id = _
  rw [List.map_id]
  fin_cases i <;> rfl

private theorem distanceRound_sumHalt (word : List DistanceRoundSymbol) :
    distanceRoundSumTag.configuration (haltList steinerUnarySharedCapRowsMachine word) =
      haltList steinerUnaryDistanceRoundMachine word := by
  apply congrArg (fun stk : Fin 7 → List DistanceRoundSymbol =>
    (⟨none,distanceRoundInitial,stk⟩ : steinerUnaryDistanceRoundMachine.Cfg))
  funext i
  change ((haltList steinerUnarySharedCapRowsMachine word).stk i).map id = _
  rw [List.map_id]
  rfl

/-- Evaluate the row totals from the compact distance-round request. -/
def steinerUnaryDistanceRoundAnswer (request : SteinerUnaryDistanceRoundRequest) : List SteinerUnaryCappedRowsSymbol :=
  steinerUnarySharedCapRowsAnswer (steinerUnaryDistanceRoundPairs request)

/-- The entire round runs in a polynomial in the supplied distance
matrix and one previous weight vector. -/
def steinerUnaryDistanceRoundMachine_run (request : SteinerUnaryDistanceRoundRequest) :
    let X := (encodeSteinerUnaryDistanceRound request).length
    let C := X^2+X
    TM2OutputsInTime steinerUnaryDistanceRoundMachine (encodeSteinerUnaryDistanceRound request)
      (some (steinerUnaryDistanceRoundAnswer request)) (12*C^2+26*C+4*X^2+7*X+11) := by
  let input := encodeSteinerUnaryDistanceRound request
  let frame := steinerUnaryDistanceRoundFrameAnswer request
  let output := steinerUnaryDistanceRoundAnswer request
  let X := input.length
  let Y := frame.length
  let C := X^2+X
  let prep := steinerUnaryDistanceRoundFrameMachine_run request
  have steps := iterate_map_some distanceRoundPrepared (fun move => distanceRound_prepStep move)
    prep.steps prep.evals_in_steps
  change (flip bind steinerUnaryDistanceRoundMachine.step)^[prep.steps]
    (some (distanceRoundPrepared (initList steinerUnaryDistanceRoundFrameMachine input))) =
    some (distanceRoundPrepared (haltList steinerUnaryDistanceRoundFrameMachine frame)) at steps
  rw [distanceRound_prepInit,distanceRound_prepReturn] at steps
  have prepared : EvalsToInTime steinerUnaryDistanceRoundMachine.step
      (initList steinerUnaryDistanceRoundMachine input) (some (distanceRoundCfg (some distanceRoundReturn) frame))
      (4*X^2+7*X+5) := ⟨⟨prep.steps,steps⟩,prep.steps_le_m⟩
  have run := steinerUnarySharedCapRowsMachine_run (steinerUnaryDistanceRoundPairs request)
  have evaluated := distanceRoundSumTag.evaluation (base := steinerUnarySharedCapRowsMachine.m)
    (host := distanceRoundProgram) (fun _ => rfl) run
  change EvalsToInTime steinerUnaryDistanceRoundMachine.step
    (distanceRoundSumTag.configuration (initList steinerUnarySharedCapRowsMachine frame))
    (some (distanceRoundSumTag.configuration (haltList steinerUnarySharedCapRowsMachine output))) (12*Y^2+26*Y+6) at evaluated
  rw [distanceRound_sumInit,distanceRound_sumHalt] at evaluated
  have all := EvalsToInTime.trans _ _ _ _ _ _ prepared evaluated
  refine ⟨all.toEvalsTo,all.steps_le_m.trans ?_⟩
  have fits : Y ≤ C := steinerUnaryDistanceRoundFrameAnswer_length_le request
  have square : Y^2 ≤ C^2 := Nat.pow_le_pow_left fits 2
  change (12*Y^2+26*Y+6)+(4*X^2+7*X+5) ≤ 12*C^2+26*C+4*X^2+7*X+11
  omega

/-- An actual polynomial for the composed finite-stack run. -/
noncomputable def steinerUnaryDistanceRoundMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryDistanceRound id steinerUnaryDistanceRoundAnswer where
  tm := steinerUnaryDistanceRoundMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time :=
    let C : Polynomial ℕ := Polynomial.X^2+Polynomial.X
    Polynomial.C 12*C^2+Polynomial.C 26*C+Polynomial.C 4*Polynomial.X^2+
      Polynomial.C 7*Polynomial.X+Polynomial.C 11
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_X,
      Polynomial.eval_C,Polynomial.eval_pow] using steinerUnaryDistanceRoundMachine_run request

/-- One compact rectangular input suffices for the exact next vector
of the selected forest orientation. -/
def steinerUnaryDistanceRoundMachine_forestRound {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) :
    let request := steinerForestDistanceRoundRequest dist h
    let X := (encodeSteinerUnaryDistanceRound request).length
    let C := X^2+X
    TM2OutputsInTime steinerUnaryDistanceRoundMachine (encodeSteinerUnaryDistanceRound request)
      (some (encodeSteinerUnaryCappedRowTallies (inwardHeightWeightRounds dist (h+1)).toList))
      (12*C^2+26*C+4*X^2+7*X+11) := by
  simpa only [steinerUnaryDistanceRoundAnswer,steinerUnaryDistanceRoundPairs_forestRound,
    steinerUnarySharedCapRowsAnswer,steinerForestSharedCapRequest_expanded,steinerUnaryCappedRowsAnswer_forestRound]
      using steinerUnaryDistanceRoundMachine_run (steinerForestDistanceRoundRequest dist h)

end OnlineReachabilityPreservers
