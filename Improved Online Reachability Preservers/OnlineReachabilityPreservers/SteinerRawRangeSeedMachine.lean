import OnlineReachabilityPreservers.SteinerRawRangeBatchMachine
import OnlineReachabilityPreservers.SteinerRangeSeedMachine

/-! Run the raw range batch before the finite seed splitter on a tagged startup input. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

abbrev SteinerRawRangeSeedSymbol := SteinerRawRangeSymbol ⊕ Option Bool

private abbrev RawBatchLabel := steinerRawRangeBatchMachine.Λ
private abbrev RawBatchRegister := steinerRawRangeBatchMachine.σ
private abbrev RawSeedRegister := steinerSeedTapeMachine.σ
private instance : Fintype RawBatchLabel := steinerRawRangeBatchMachine.ΛFin

private inductive RawRangeSeedLabel where
  | collect
  | restore
  | range (label : RawBatchLabel)
  | chooseSeed
  | seed (label : Fin 4)
  deriving Fintype

private abbrev RawRangeSeedRegister := Option SteinerRawRangeSeedSymbol × RawBatchRegister × RawSeedRegister
private abbrev RawRangeSeedProgram :=
  Turing.TM2.Stmt (fun _ : Fin 5 => SteinerRawRangeSeedSymbol) RawRangeSeedLabel RawRangeSeedRegister

private def rawRangeSeedInitial : RawRangeSeedRegister :=
  (none,steinerRawRangeBatchMachine.initialState,steinerSeedTapeMachine.initialState)

private def rawRangeSeedObserve (_ : RawRangeSeedRegister) (seen : Option SteinerRawRangeSeedSymbol) :
    RawRangeSeedRegister :=
  (seen,steinerRawRangeBatchMachine.initialState,steinerSeedTapeMachine.initialState)

private def rawSetupReadRange : SteinerRawRangeSeedSymbol → Option SteinerRawRangeSymbol
  | .inl symbol => some symbol
  | .inr _ => none

private def rawSetupReadFlag : Option SteinerRawRangeSeedSymbol → Bool
  | some (.inl (some (some flag))) => flag
  | _ => false

private def rawSetupRangeTag :
    StackMachineTag SteinerRawRangeSymbol SteinerRawRangeSeedSymbol RawBatchLabel RawRangeSeedLabel
      RawBatchRegister RawRangeSeedRegister where
  writeSymbol := Sum.inl
  readSymbol := rawSetupReadRange
  writeRegister r := (none,r,steinerSeedTapeMachine.initialState)
  readRegister r := r.2.1
  writeLabel := RawRangeSeedLabel.range
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def rawSetupRangeSlots : Fin 4 ↪ Fin 5 :=
  ⟨Fin.castSucc,Fin.castSucc_injective _⟩

private def rawSetupSeedTag :
    StackMachineTag (Option Bool) SteinerRawRangeSeedSymbol (Fin 4) RawRangeSeedLabel
      RawSeedRegister RawRangeSeedRegister where
  writeSymbol := Sum.inr
  readSymbol
    | .inl _ => none
    | .inr bit => some bit
  writeRegister r := (none,steinerRawRangeBatchMachine.initialState,r)
  readRegister r := r.2.2
  writeLabel := RawRangeSeedLabel.seed
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def rawSetupSeedSlots : Fin 3 ↪ Fin 5 where
  toFun := ![4,1,2]
  inj' := by
    intro i j same
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction

private def rawSetupRangeInner :
    RawRangeSeedLabel → StackMachineTag.Program (Fin 4) SteinerRawRangeSeedSymbol RawRangeSeedLabel RawRangeSeedRegister
  | .range l => rawSetupRangeTag.returningStatement .chooseSeed (steinerRawRangeBatchMachine.m l)
  | _ => halt

private def rawSetupSeedFramed (l : Fin 4) :
    StackMachineTag.Program (Fin 5) (Option Bool) (Fin 4) RawSeedRegister :=
  StackIndexEmbedding.statement rawSetupSeedSlots (steinerSeedTapeMachine.m l)

private def rawRangeSeedProgram : RawRangeSeedLabel → RawRangeSeedProgram
  | .collect =>
    peek 4 rawRangeSeedObserve <|
      branch (fun r => (r.1.bind rawSetupReadRange).isSome)
        (pop 4 (fun r _ => r) <| push 0 (fun r => r.1.getD (Sum.inl none)) <|
          load (fun _ => rawRangeSeedInitial) <| goto (fun _ => .collect))
        (load (fun _ => rawRangeSeedInitial) <| goto (fun _ => .restore))
  | .restore =>
    pop 0 rawRangeSeedObserve <|
      branch (fun r => r.1.isSome)
        (push 3 (fun r => r.1.getD (Sum.inl none)) <| load (fun _ => rawRangeSeedInitial) <| goto (fun _ => .restore))
        (load (fun _ => rawRangeSeedInitial) <| goto (fun _ => .range steinerRawRangeBatchMachine.main))
  | .range l => StackIndexEmbedding.statement rawSetupRangeSlots (rawSetupRangeInner (.range l))
  | .chooseSeed =>
    pop 3 rawRangeSeedObserve <|
      branch (fun r => rawSetupReadFlag r.1)
        (load (fun _ => rawRangeSeedInitial) <| goto (fun _ => .seed 0))
        (push 4 (fun _ => Sum.inl none) <| load (fun _ => rawRangeSeedInitial) halt)
  | .seed l => rawSetupSeedTag.statement (rawSetupSeedFramed l)

/-- Check the raw framed batch before running the seed splitter. Graph
rejection preserves the complete seed frame behind a rejection marker. -/
abbrev steinerRawRangeSeedMachine : FinTM2 where
  K := Fin 5
  k₀ := 4
  k₁ := 4
  Γ _ := SteinerRawRangeSeedSymbol
  Λ := RawRangeSeedLabel
  main := .collect
  σ := RawRangeSeedRegister
  initialState := rawRangeSeedInitial
  m := rawRangeSeedProgram

private def rawSetupCfg (label : Option RawRangeSeedLabel)
    (buffer checked input : List SteinerRawRangeSeedSymbol) : steinerRawRangeSeedMachine.Cfg where
  l := label
  var := rawRangeSeedInitial
  stk := ![buffer,[],[],checked,input]

private theorem rawSetup_update0 (a b q next : List SteinerRawRangeSeedSymbol) :
    Function.update (![a,[],[],b,q] : Fin 5 → List SteinerRawRangeSeedSymbol) 0 next = ![next,[],[],b,q] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem rawSetup_update3 (a b q next : List SteinerRawRangeSeedSymbol) :
    Function.update (![a,[],[],b,q] : Fin 5 → List SteinerRawRangeSeedSymbol) 3 next = ![a,[],[],next,q] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem rawSetup_update4 (a b q next : List SteinerRawRangeSeedSymbol) :
    Function.update (![a,[],[],b,q] : Fin 5 → List SteinerRawRangeSeedSymbol) 4 next = ![a,[],[],b,next] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem rawSetup_collectSymbol (symbol : SteinerRawRangeSymbol) (buffer tail : List SteinerRawRangeSeedSymbol) :
    steinerRawRangeSeedMachine.step (rawSetupCfg (some .collect) buffer [] (Sum.inl symbol::tail)) =
      some (rawSetupCfg (some .collect) (Sum.inl symbol::buffer) [] tail) := by
  simp [FinTM2.step,steinerRawRangeSeedMachine,rawSetupCfg,Turing.TM2.step,Turing.TM2.stepAux,
    rawRangeSeedProgram,rawRangeSeedObserve,rawSetupReadRange,rawSetup_update0,rawSetup_update4]
  rfl

private theorem rawSetup_collectDone (buffer : List SteinerRawRangeSeedSymbol) (seed : List (Option Bool)) :
    steinerRawRangeSeedMachine.step (rawSetupCfg (some .collect) buffer [] (seed.map Sum.inr)) =
      some (rawSetupCfg (some .restore) buffer [] (seed.map Sum.inr)) := by
  cases seed <;>
    simp [FinTM2.step,steinerRawRangeSeedMachine,rawSetupCfg,Turing.TM2.step,Turing.TM2.stepAux,
      rawRangeSeedProgram,rawRangeSeedObserve,rawSetupReadRange] <;> rfl

private theorem rawSetup_restoreSymbol (symbol : SteinerRawRangeSeedSymbol)
    (buffer checked input : List SteinerRawRangeSeedSymbol) :
    steinerRawRangeSeedMachine.step (rawSetupCfg (some .restore) (symbol::buffer) checked input) =
      some (rawSetupCfg (some .restore) buffer (symbol::checked) input) := by
  simp [FinTM2.step,steinerRawRangeSeedMachine,rawSetupCfg,Turing.TM2.step,Turing.TM2.stepAux,
    rawRangeSeedProgram,rawRangeSeedObserve,rawSetup_update0,rawSetup_update3]
  rfl

private theorem rawSetup_restoreDone (checked input : List SteinerRawRangeSeedSymbol) :
    steinerRawRangeSeedMachine.step (rawSetupCfg (some .restore) [] checked input) =
      some (rawSetupCfg (some (.range steinerRawRangeBatchMachine.main)) [] checked input) := by
  simp [FinTM2.step,steinerRawRangeSeedMachine,rawSetupCfg,Turing.TM2.step,Turing.TM2.stepAux,
    rawRangeSeedProgram,rawRangeSeedObserve,rawSetup_update0]
  rfl

private theorem rawSetup_choose (accepted : Bool) (seed : List (Option Bool)) :
    steinerRawRangeSeedMachine.step
      (rawSetupCfg (some .chooseSeed) [] ((encodeSteinerRawRangeAnswer accepted).map Sum.inl) (seed.map Sum.inr)) =
      some (if accepted then rawSetupCfg (some (.seed 0)) [] [] (seed.map Sum.inr)
        else rawSetupCfg none [] [] (Sum.inl none::seed.map Sum.inr)) := by
  cases accepted <;>
    simp [FinTM2.step,steinerRawRangeSeedMachine,rawSetupCfg,Turing.TM2.step,Turing.TM2.stepAux,
      rawRangeSeedProgram,rawRangeSeedObserve,rawSetupReadFlag,encodeSteinerRawRangeAnswer,rawSetup_update3,rawSetup_update4] <;> rfl

private def rawSetupOne {a b : steinerRawRangeSeedMachine.Cfg}
    (step : steinerRawRangeSeedMachine.step a = some b) :
    EvalsToInTime steinerRawRangeSeedMachine.step a (some b) 1 where
  steps := 1
  evals_in_steps := by change steinerRawRangeSeedMachine.step a = some b; exact step
  steps_le_m := le_rfl

private def rawSetup_collect (range : List SteinerRawRangeSymbol) (buffer : List SteinerRawRangeSeedSymbol)
    (seed : List (Option Bool)) :
    EvalsToInTime steinerRawRangeSeedMachine.step
      (rawSetupCfg (some .collect) buffer [] (range.map Sum.inl ++ seed.map Sum.inr))
      (some (rawSetupCfg (some .restore) ((range.map Sum.inl).reverse++buffer) [] (seed.map Sum.inr)))
      (range.length+1) := by
  induction range generalizing buffer with
  | nil => exact rawSetupOne (rawSetup_collectDone buffer seed)
  | cons symbol range ih =>
    have first := rawSetupOne (rawSetup_collectSymbol symbol buffer (range.map Sum.inl ++ seed.map Sum.inr))
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (Sum.inl symbol::buffer))
    simpa only [List.map_cons,List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,
      List.nil_append,List.length_cons] using all

private def rawSetup_restore (buffer checked input : List SteinerRawRangeSeedSymbol) :
    EvalsToInTime steinerRawRangeSeedMachine.step (rawSetupCfg (some .restore) buffer checked input)
      (some (rawSetupCfg (some (.range steinerRawRangeBatchMachine.main)) [] (buffer.reverse++checked) input))
      (buffer.length+1) := by
  induction buffer generalizing checked with
  | nil => exact rawSetupOne (rawSetup_restoreDone checked input)
  | cons symbol buffer ih =>
    have first := rawSetupOne (rawSetup_restoreSymbol symbol buffer checked input)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (symbol::checked))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons] using all

private def rawSetupPassive (tail : List SteinerRawRangeSeedSymbol) (i : Fin 5) : List SteinerRawRangeSeedSymbol :=
  if i = 4 then tail else []

private theorem rawSetupRangeSlots_excludes_input (i : Fin 4) : rawSetupRangeSlots i ≠ 4 := by
  fin_cases i <;> decide

private noncomputable def rawSetupRangeTranslated (seed : List (Option Bool))
    (c : steinerRawRangeBatchMachine.Cfg) : steinerRawRangeSeedMachine.Cfg :=
  StackIndexEmbedding.configuration rawSetupRangeSlots (rawSetupPassive (seed.map Sum.inr))
    (rawSetupRangeTag.returningConfiguration .chooseSeed c)

private theorem rawSetup_translateRangeStep (seed : List (Option Bool))
    {c after : steinerRawRangeBatchMachine.Cfg} (step : steinerRawRangeBatchMachine.step c = some after) :
    steinerRawRangeSeedMachine.step (rawSetupRangeTranslated seed c) = some (rawSetupRangeTranslated seed after) := by
  have tagged := rawSetupRangeTag.step_embedded_return .chooseSeed (base := steinerRawRangeBatchMachine.m)
    (host := rawSetupRangeInner) (fun _ => rfl) step
  have framed := StackIndexEmbedding.step_on rawSetupRangeSlots (base := rawSetupRangeInner)
    (rawSetupPassive (seed.map Sum.inr)) (rawSetupRangeTag.returningConfiguration .chooseSeed c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem rawSetup_rangeInit (tape : List SteinerRawRangeSymbol) (seed : List (Option Bool)) :
    rawSetupRangeTranslated seed (initList steinerRawRangeBatchMachine tape) =
      rawSetupCfg (some (.range steinerRawRangeBatchMachine.main)) [] (tape.map Sum.inl) (seed.map Sum.inr) := by
  apply congrArg (fun stk : Fin 5 → List SteinerRawRangeSeedSymbol =>
    (⟨some (.range steinerRawRangeBatchMachine.main),rawRangeSeedInitial,stk⟩ : steinerRawRangeSeedMachine.Cfg))
  funext i
  fin_cases i
  · change StackIndexEmbedding.tapesAt rawSetupRangeSlots _ _ (rawSetupRangeSlots 0) = _
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change StackIndexEmbedding.tapesAt rawSetupRangeSlots _ _ (rawSetupRangeSlots 1) = _
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change StackIndexEmbedding.tapesAt rawSetupRangeSlots _ _ (rawSetupRangeSlots 2) = _
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change StackIndexEmbedding.tapesAt rawSetupRangeSlots _ _ (rawSetupRangeSlots 3) = _
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change StackIndexEmbedding.tapesAt rawSetupRangeSlots _ (rawSetupPassive (seed.map Sum.inr)) 4 = _
    rw [StackIndexEmbedding.tapesAt_extra _ _ _ rawSetupRangeSlots_excludes_input,rawSetupPassive,ite_eq_left rfl]
    rfl

private theorem rawSetup_rangeReturn (out : List SteinerRawRangeSymbol) (seed : List (Option Bool)) :
    rawSetupRangeTranslated seed (haltList steinerRawRangeBatchMachine out) =
      rawSetupCfg (some .chooseSeed) [] (out.map Sum.inl) (seed.map Sum.inr) := by
  apply congrArg (fun stk : Fin 5 → List SteinerRawRangeSeedSymbol =>
    (⟨some .chooseSeed,rawRangeSeedInitial,stk⟩ : steinerRawRangeSeedMachine.Cfg))
  funext i
  fin_cases i
  · change StackIndexEmbedding.tapesAt rawSetupRangeSlots _ _ (rawSetupRangeSlots 0) = _
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change StackIndexEmbedding.tapesAt rawSetupRangeSlots _ _ (rawSetupRangeSlots 1) = _
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change StackIndexEmbedding.tapesAt rawSetupRangeSlots _ _ (rawSetupRangeSlots 2) = _
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change StackIndexEmbedding.tapesAt rawSetupRangeSlots _ _ (rawSetupRangeSlots 3) = _
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change StackIndexEmbedding.tapesAt rawSetupRangeSlots _ (rawSetupPassive (seed.map Sum.inr)) 4 = _
    rw [StackIndexEmbedding.tapesAt_extra _ _ _ rawSetupRangeSlots_excludes_input,rawSetupPassive,ite_eq_left rfl]
    rfl

private def rawSetup_rangeEval (checks : List SteinerRangeWordPair) (seed : List (Option Bool)) :
    EvalsToInTime steinerRawRangeSeedMachine.step
      (rawSetupCfg (some (.range steinerRawRangeBatchMachine.main)) []
        ((encodeSteinerRawRangeBatch checks).map Sum.inl) (seed.map Sum.inr))
      (some (rawSetupCfg (some .chooseSeed) []
        ((encodeSteinerRawRangeAnswer (steinerRangeChecks checks)).map Sum.inl) (seed.map Sum.inr)))
      (5*(encodeSteinerRawRangeBatch checks).length+1) := by
  let run := steinerRawRangeBatchMachine_run checks
  refine ⟨⟨run.steps,?_⟩,run.steps_le_m⟩
  have executed := iterate_map_some (rawSetupRangeTranslated seed) (fun step => rawSetup_translateRangeStep seed step)
    run.steps run.evals_in_steps
  change (flip bind steinerRawRangeSeedMachine.step)^[run.steps]
      (some (rawSetupRangeTranslated seed (initList steinerRawRangeBatchMachine (encodeSteinerRawRangeBatch checks)))) =
    some (rawSetupRangeTranslated seed
      (haltList steinerRawRangeBatchMachine (encodeSteinerRawRangeAnswer (steinerRangeChecks checks)))) at executed
  rw [rawSetup_rangeInit,rawSetup_rangeReturn] at executed
  exact executed

private theorem rawSetupSeedSlots_zero : rawSetupSeedSlots 0 = 4 := by decide
private theorem rawSetupSeedSlots_one : rawSetupSeedSlots 1 = 1 := by decide
private theorem rawSetupSeedSlots_two : rawSetupSeedSlots 2 = 2 := by decide

private theorem rawSetupSeedSlots_excludes_first (i : Fin 3) : rawSetupSeedSlots i ≠ 0 := by
  fin_cases i <;> decide

private theorem rawSetupSeedSlots_excludes_fourth (i : Fin 3) : rawSetupSeedSlots i ≠ 3 := by
  fin_cases i <;> decide

private noncomputable def rawSetupSeedTranslated (c : steinerSeedTapeMachine.Cfg) : steinerRawRangeSeedMachine.Cfg :=
  rawSetupSeedTag.configuration (StackIndexEmbedding.configuration rawSetupSeedSlots (fun _ => []) c)

private theorem rawSetupSeedTranslated_tape (c : steinerSeedTapeMachine.Cfg) (k : Fin 3) :
    (rawSetupSeedTranslated c).stk (rawSetupSeedSlots k) = (c.stk k).map Sum.inr :=
  congrArg (List.map Sum.inr) (StackIndexEmbedding.tapesAt_image rawSetupSeedSlots c.stk (fun _ => []) k)

private theorem rawSetup_seedInit (seed : List (Option Bool)) :
    rawSetupSeedTranslated (initList steinerSeedTapeMachine seed) =
      rawSetupCfg (some (.seed 0)) [] [] (seed.map Sum.inr) := by
  apply congrArg (fun stk : Fin 5 → List SteinerRawRangeSeedSymbol =>
    (⟨some (.seed 0),rawRangeSeedInitial,stk⟩ : steinerRawRangeSeedMachine.Cfg))
  funext i
  fin_cases i
  · change (StackIndexEmbedding.tapesAt rawSetupSeedSlots _ (fun _ => []) 0).map Sum.inr = []
    rw [StackIndexEmbedding.tapesAt_extra _ _ _ rawSetupSeedSlots_excludes_first]
    rfl
  · have taped := rawSetupSeedTranslated_tape (initList steinerSeedTapeMachine seed) 1
    rw [rawSetupSeedSlots_one] at taped
    exact taped
  · have taped := rawSetupSeedTranslated_tape (initList steinerSeedTapeMachine seed) 2
    rw [rawSetupSeedSlots_two] at taped
    exact taped
  · change (StackIndexEmbedding.tapesAt rawSetupSeedSlots _ (fun _ => []) 3).map Sum.inr = []
    rw [StackIndexEmbedding.tapesAt_extra _ _ _ rawSetupSeedSlots_excludes_fourth]
    rfl
  · have taped := rawSetupSeedTranslated_tape (initList steinerSeedTapeMachine seed) 0
    rw [rawSetupSeedSlots_zero] at taped
    exact taped

private theorem rawSetup_seedHalt (out : List (Option Bool)) :
    rawSetupSeedTranslated (haltList steinerSeedTapeMachine out) =
      rawSetupCfg none [] [] (out.map Sum.inr) := by
  apply congrArg (fun stk : Fin 5 → List SteinerRawRangeSeedSymbol =>
    (⟨none,rawRangeSeedInitial,stk⟩ : steinerRawRangeSeedMachine.Cfg))
  funext i
  fin_cases i
  · change (StackIndexEmbedding.tapesAt rawSetupSeedSlots _ (fun _ => []) 0).map Sum.inr = []
    rw [StackIndexEmbedding.tapesAt_extra _ _ _ rawSetupSeedSlots_excludes_first]
    rfl
  · have taped := rawSetupSeedTranslated_tape (haltList steinerSeedTapeMachine out) 1
    rw [rawSetupSeedSlots_one] at taped
    exact taped
  · have taped := rawSetupSeedTranslated_tape (haltList steinerSeedTapeMachine out) 2
    rw [rawSetupSeedSlots_two] at taped
    exact taped
  · change (StackIndexEmbedding.tapesAt rawSetupSeedSlots _ (fun _ => []) 3).map Sum.inr = []
    rw [StackIndexEmbedding.tapesAt_extra _ _ _ rawSetupSeedSlots_excludes_fourth]
    rfl
  · have taped := rawSetupSeedTranslated_tape (haltList steinerSeedTapeMachine out) 0
    rw [rawSetupSeedSlots_zero] at taped
    exact taped

private def rawSetup_seedEval (seed out : List (Option Bool)) {bound : ℕ}
    (run : TM2OutputsInTime steinerSeedTapeMachine seed (some out) bound) :
    EvalsToInTime steinerRawRangeSeedMachine.step (rawSetupCfg (some (.seed 0)) [] [] (seed.map Sum.inr))
      (some (rawSetupCfg none [] [] (out.map Sum.inr))) bound := by
  refine ⟨⟨run.steps,?_⟩,run.steps_le_m⟩
  let framed := StackIndexEmbedding.evaluation rawSetupSeedSlots (base := steinerSeedTapeMachine.m) (fun _ => []) run
  let tagged := rawSetupSeedTag.evaluation (base := rawSetupSeedFramed) (host := rawRangeSeedProgram) (fun _ => rfl) framed
  have executed : (flip bind steinerRawRangeSeedMachine.step)^[run.steps]
      (some (rawSetupSeedTranslated (initList steinerSeedTapeMachine seed))) =
    some (rawSetupSeedTranslated (haltList steinerSeedTapeMachine out)) :=
    tagged.evals_in_steps
  rw [rawSetup_seedInit,rawSetup_seedHalt] at executed
  exact executed

private def rawSetup_checkEvaluates (checks : List SteinerRangeWordPair) (seed : List (Option Bool)) :
    EvalsToInTime steinerRawRangeSeedMachine.step
      (rawSetupCfg (some .collect) [] [] ((encodeSteinerRawRangeBatch checks).map Sum.inl ++ seed.map Sum.inr))
      (some (rawSetupCfg (some .chooseSeed) []
        ((encodeSteinerRawRangeAnswer (steinerRangeChecks checks)).map Sum.inl) (seed.map Sum.inr)))
      (7*(encodeSteinerRawRangeBatch checks).length+3) := by
  let frame := encodeSteinerRawRangeBatch checks
  have collected := rawSetup_collect frame [] seed
  rw [List.append_nil] at collected
  have restored := rawSetup_restore (frame.map Sum.inl).reverse [] (seed.map Sum.inr)
  rw [List.reverse_reverse,List.append_nil,List.length_reverse,List.length_map] at restored
  have prepared := EvalsToInTime.trans _ _ _ _ _ _ collected restored
  have checked := EvalsToInTime.trans _ _ _ _ _ _ prepared (rawSetup_rangeEval checks seed)
  refine ⟨checked.toEvalsTo,?_⟩
  have spent := checked.steps_le_m
  change checked.steps ≤ (5*frame.length+1)+((frame.length+1)+(frame.length+1)) at spent
  change checked.steps ≤ 7*frame.length+3
  omega

private theorem rawSetup_init (tape : List SteinerRawRangeSeedSymbol) :
    initList steinerRawRangeSeedMachine tape = rawSetupCfg (some .collect) [] [] tape := by
  unfold initList rawSetupCfg
  apply congrArg (fun stk : Fin 5 → List SteinerRawRangeSeedSymbol =>
    (⟨some .collect,rawRangeSeedInitial,stk⟩ : steinerRawRangeSeedMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem rawSetup_halt (out : List SteinerRawRangeSeedSymbol) :
    haltList steinerRawRangeSeedMachine out = rawSetupCfg none [] [] out := by
  unfold haltList rawSetupCfg
  apply congrArg (fun stk : Fin 5 → List SteinerRawRangeSeedSymbol =>
    (⟨none,rawRangeSeedInitial,stk⟩ : steinerRawRangeSeedMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- Keep the raw range frames and the unary seed frame in separate symbol tags. -/
def encodeSteinerRawRangeSeed (request : SteinerRangeSeedRequest) : List SteinerRawRangeSeedSymbol :=
  (encodeSteinerRawRangeBatch request.1).map Sum.inl ++ (encodeSteinerSeedTapeRequest request.2).map Sum.inr

/-- Graph rejection keeps the seed request. Graph acceptance returns
the encoded seed result, which is empty on exhaustion. -/
def encodeSteinerRawRangeSeedAnswer (accepted : Bool) (seedRequest seedOutput : List (Option Bool)) :
    List SteinerRawRangeSeedSymbol :=
  if accepted then seedOutput.map Sum.inr else Sum.inl none::seedRequest.map Sum.inr

def steinerRawRangeSeedAnswer (request : SteinerRangeSeedRequest) : List SteinerRawRangeSeedSymbol :=
  encodeSteinerRawRangeSeedAnswer (steinerRangeChecks request.1)
    (encodeSteinerSeedTapeRequest request.2) (splitSteinerSeedTapeOrReject request.2)

private def rawSetup_finishRejected (seed : List (Option Bool)) {start : steinerRawRangeSeedMachine.Cfg}
    {checkTime : ℕ} (checked : EvalsToInTime steinerRawRangeSeedMachine.step start
      (some (rawSetupCfg (some .chooseSeed) [] ((encodeSteinerRawRangeAnswer false).map Sum.inl) (seed.map Sum.inr)))
      checkTime) :
    EvalsToInTime steinerRawRangeSeedMachine.step start
      (some (haltList steinerRawRangeSeedMachine (Sum.inl none::seed.map Sum.inr))) (checkTime+1) := by
  rw [rawSetup_halt]
  have all := EvalsToInTime.trans _ _ _ _ _ _ checked (rawSetupOne (rawSetup_choose false seed))
  exact ⟨all.toEvalsTo,by have spent := all.steps_le_m; omega⟩

private def rawSetup_finishChecked (accepted : Bool) (seed out : List (Option Bool))
    {start : steinerRawRangeSeedMachine.Cfg} {checkTime seedTime : ℕ}
    (checked : EvalsToInTime steinerRawRangeSeedMachine.step start
      (some (rawSetupCfg (some .chooseSeed) []
        ((encodeSteinerRawRangeAnswer accepted).map Sum.inl) (seed.map Sum.inr))) checkTime)
    (seedRun : TM2OutputsInTime steinerSeedTapeMachine seed (some out) seedTime) :
    EvalsToInTime steinerRawRangeSeedMachine.step start
      (some (haltList steinerRawRangeSeedMachine (encodeSteinerRawRangeSeedAnswer accepted seed out)))
      (checkTime+seedTime+1) := by
  cases accepted
  · have all := rawSetup_finishRejected seed checked
    exact ⟨all.toEvalsTo,by have spent := all.steps_le_m; omega⟩
  · rw [rawSetup_halt]
    have choose := rawSetupOne (rawSetup_choose true seed)
    have prepared := EvalsToInTime.trans _ _ _ _ _ _ checked choose
    have all := EvalsToInTime.trans _ _ _ _ _ _ prepared (rawSetup_seedEval seed out seedRun)
    exact ⟨all.toEvalsTo,by have spent := all.steps_le_m; omega⟩

private def rawSetup_execute (checks : List SteinerRangeWordPair) (seed out : List (Option Bool)) {bound : ℕ}
    (seedRun : TM2OutputsInTime steinerSeedTapeMachine seed (some out) bound) :
    TM2OutputsInTime steinerRawRangeSeedMachine ((encodeSteinerRawRangeBatch checks).map Sum.inl ++ seed.map Sum.inr)
      (some (encodeSteinerRawRangeSeedAnswer (steinerRangeChecks checks) seed out))
      (7*(encodeSteinerRawRangeBatch checks).length+bound+4) := by
  change EvalsToInTime steinerRawRangeSeedMachine.step _ (some (haltList steinerRawRangeSeedMachine _)) _
  rw [rawSetup_init]
  have all := rawSetup_finishChecked (steinerRangeChecks checks) seed out (rawSetup_checkEvaluates checks seed) seedRun
  exact ⟨all.toEvalsTo,by have spent := all.steps_le_m; omega⟩

/-- The composed machine implements graph rejection, accepted seed
prefixes, and seed exhaustion on the supplied raw frames. -/
def steinerRawRangeSeedMachine_run (request : SteinerRangeSeedRequest) :
    TM2OutputsInTime steinerRawRangeSeedMachine (encodeSteinerRawRangeSeed request)
      (some (steinerRawRangeSeedAnswer request))
      (7*(encodeSteinerRawRangeBatch request.1).length+3*request.2.1+7) := by
  have run := rawSetup_execute request.1 (encodeSteinerSeedTapeRequest request.2)
    (splitSteinerSeedTapeOrReject request.2) (steinerSeedTapeMachine_runOrReject request.2)
  exact ⟨run.toEvalsTo,by have spent := run.steps_le_m; omega⟩

/-- A linear bound in the complete tagged startup encoding. -/
noncomputable def steinerRawRangeSeedMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerRawRangeSeed id steinerRawRangeSeedAnswer where
  tm := steinerRawRangeSeedMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 7*Polynomial.X+Polynomial.C 7
  outputsFun request := by
    have run := steinerRawRangeSeedMachine_run request
    have length : (encodeSteinerRawRangeSeed request).length =
        (encodeSteinerRawRangeBatch request.1).length+request.2.1+request.2.2.length := by
      simp [encodeSteinerRawRangeSeed,encodeSteinerSeedTapeRequest,Nat.add_assoc]
    have fits : 7*(encodeSteinerRawRangeBatch request.1).length+3*request.2.1+7 ≤
        (Polynomial.C 7*Polynomial.X+Polynomial.C 7).eval (encodeSteinerRawRangeSeed request).length := by
      simp only [Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_X,Polynomial.eval_C,length]
      omega
    change TM2OutputsInTime steinerRawRangeSeedMachine ((encodeSteinerRawRangeSeed request).map id)
      (some ((steinerRawRangeSeedAnswer request).map id)) _
    simpa only [List.map_id_fun,id_eq] using
      (show TM2OutputsInTime steinerRawRangeSeedMachine (encodeSteinerRawRangeSeed request)
        (some (steinerRawRangeSeedAnswer request)) _ from ⟨run.toEvalsTo,run.steps_le_m.trans fits⟩)

/-- With a supplied bound of value n, the raw machine agrees with the
guarded decoder at allowance n plus the total endpoint bit count. It
runs the verified finite sampler when the guarded decoder accepts. -/
def steinerRawRangeSeedMachine_guardedSampler {n size : ℕ} (bound : List Bool)
    (number : binaryWordValue bound = n) (rows : List SteinerRangeWordPair)
    (count : {b : ℕ // b = size}) (tape : List Bool) :
    TM2OutputsInTime steinerRawRangeSeedMachine
      (encodeSteinerRawRangeSeed (steinerRangeRequests bound rows,(size,tape)))
      (some (encodeSteinerRawRangeSeedAnswer
        ((decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1.isSome)
        (encodeSteinerSeedTapeRequest (size,tape))
        ((((readSteinerSeedWithWork count steinerBitTapeSource).run tape).map encodeSavedSteinerSeed).getD [])))
      (7*(binaryEndpointBits rows+2*rows.length*(bound.length+2))+3*size+7) := by
  rw [← steinerRangeRequests_guarded_flag bound number rows,← encodeSteinerRawRangeRequests_length]
  have run := rawSetup_execute (steinerRangeRequests bound rows) (encodeSteinerSeedTapeRequest (size,tape)) _
    (steinerSeedTapeMachine_refinesFiniteSampler count tape)
  exact ⟨run.toEvalsTo,by have spent := run.steps_le_m; omega⟩

/-- On graph rejection the raw machine never activates the seed
subroutine. The rejection bound is independent of the seed frame. -/
def steinerRawRangeSeedMachine_rejectedGraph (request : SteinerRangeSeedRequest)
    (rejected : steinerRangeChecks request.1 = false) :
    TM2OutputsInTime steinerRawRangeSeedMachine (encodeSteinerRawRangeSeed request)
      (some (Sum.inl none::(encodeSteinerSeedTapeRequest request.2).map Sum.inr))
      (7*(encodeSteinerRawRangeBatch request.1).length+4) := by
  let seed := encodeSteinerSeedTapeRequest request.2
  have checked := rawSetup_checkEvaluates request.1 seed
  rw [rejected] at checked
  change EvalsToInTime steinerRawRangeSeedMachine.step _ (some (haltList steinerRawRangeSeedMachine _)) _
  rw [rawSetup_init]
  exact rawSetup_finishRejected seed checked

/-- Enter the range check with its raw frame on the graph stack and the
complete seed frame on the input stack. -/
def steinerRawRangeSeedPrepared (frame : List SteinerRawRangeSymbol) (seed : List (Option Bool)) :
    steinerRawRangeSeedMachine.Cfg :=
  rawSetupCfg (some (.range steinerRawRangeBatchMachine.main)) [] (frame.map Sum.inl) (seed.map Sum.inr)

/-- Start the check directly on the placed frames. The seed evaluation
is used only when all range comparisons succeed. -/
def steinerRawRangeSeedMachine_finishPrepared (checks : List SteinerRangeWordPair) (seed out : List (Option Bool))
    {bound : ℕ} (seedRun : TM2OutputsInTime steinerSeedTapeMachine seed (some out) bound) :
    EvalsToInTime steinerRawRangeSeedMachine.step
      (steinerRawRangeSeedPrepared (encodeSteinerRawRangeBatch checks) seed)
      (some (haltList steinerRawRangeSeedMachine (encodeSteinerRawRangeSeedAnswer (steinerRangeChecks checks) seed out)))
      (5*(encodeSteinerRawRangeBatch checks).length+bound+2) := by
  have all := rawSetup_finishChecked (steinerRangeChecks checks) seed out (rawSetup_rangeEval checks seed) seedRun
  exact ⟨all.toEvalsTo,by have spent := all.steps_le_m; omega⟩

/-- A prepared graph rejection has a bound independent of the seed
frame and preserves that frame behind the rejection marker. -/
def steinerRawRangeSeedMachine_finishRejected (checks : List SteinerRangeWordPair) (seed : List (Option Bool))
    (rejected : steinerRangeChecks checks = false) :
    EvalsToInTime steinerRawRangeSeedMachine.step
      (steinerRawRangeSeedPrepared (encodeSteinerRawRangeBatch checks) seed)
      (some (haltList steinerRawRangeSeedMachine (Sum.inl none::seed.map Sum.inr)))
      (5*(encodeSteinerRawRangeBatch checks).length+2) := by
  have checked := rawSetup_rangeEval checks seed
  rw [rejected] at checked
  exact rawSetup_finishRejected seed checked

end OnlineReachabilityPreservers
