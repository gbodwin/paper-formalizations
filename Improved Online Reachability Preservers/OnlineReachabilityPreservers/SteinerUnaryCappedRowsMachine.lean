import OnlineReachabilityPreservers.SteinerUnaryCappedSumMachine

/-! Evaluate all capped transfers of each supplied root row. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev CappedRowsBaseLabel := steinerUnaryCappedSumMachine.Λ
private abbrev CappedRowsBaseRegister := steinerUnaryCappedSumMachine.σ
private instance : Fintype CappedRowsBaseLabel := steinerUnaryCappedSumMachine.ΛFin

private inductive CappedRowsLabel where
  | read
  | restore
  | cell (label : CappedRowsBaseLabel)
  | emit
  | finish
  deriving Fintype

abbrev SteinerUnaryCappedRowsSymbol := Bool ⊕ Option Bool
private abbrev CappedRowsRegister := Option SteinerUnaryCappedRowsSymbol × CappedRowsBaseRegister
private abbrev CappedRowsProgram :=
  StackMachineTag.Program (Fin 7) SteinerUnaryCappedRowsSymbol CappedRowsLabel CappedRowsRegister

private def cappedRowsInitial : CappedRowsRegister := (none,steinerUnaryCappedSumMachine.initialState)

private def cappedRowsObserve (_ : CappedRowsRegister) (seen : Option SteinerUnaryCappedRowsSymbol) :
    CappedRowsRegister := (seen,steinerUnaryCappedSumMachine.initialState)

private def cappedRowsNext (label : CappedRowsLabel) : CappedRowsProgram :=
  load (fun _ => cappedRowsInitial) (goto (fun _ => label))

private def cappedRowsPayload : SteinerUnaryCappedRowsSymbol → Option (Option Bool)
  | .inl _ => none
  | .inr value => some value

private def cappedRowsTag :
    StackMachineTag (Option Bool) SteinerUnaryCappedRowsSymbol CappedRowsBaseLabel CappedRowsLabel
      CappedRowsBaseRegister CappedRowsRegister where
  writeSymbol := Sum.inr
  readSymbol := cappedRowsPayload
  writeRegister r := (none,r)
  readRegister := Prod.snd
  writeLabel := .cell
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def cappedRowsSlots : Fin 5 ↪ Fin 7 :=
  ⟨fun i => i.castSucc.castSucc,(Fin.castSucc_injective 6).comp (Fin.castSucc_injective 5)⟩

private def cappedRowsInner :
    CappedRowsLabel → StackMachineTag.Program (Fin 5) SteinerUnaryCappedRowsSymbol CappedRowsLabel CappedRowsRegister
  | .cell label => cappedRowsTag.returningStatement .emit (steinerUnaryCappedSumMachine.m label)
  | _ => halt

private def cappedRowsEndOfCell : SteinerUnaryCappedRowsSymbol := Sum.inl false
private def cappedRowsEndOfRow : SteinerUnaryCappedRowsSymbol := Sum.inl true
private def cappedRowsTally : SteinerUnaryCappedRowsSymbol := Sum.inr (some true)

private def cappedRowsForward (register : CappedRowsRegister) : SteinerUnaryCappedRowsSymbol :=
  register.1.getD cappedRowsEndOfCell

private def cappedRowsProgram : CappedRowsLabel → CappedRowsProgram
  | .read =>
    pop 5 cappedRowsObserve <|
      branch (fun r => r.1.isSome)
        (branch (fun r => (r.1.bind cappedRowsPayload).isSome)
          (push 0 cappedRowsForward (cappedRowsNext .read))
          (branch (fun r => r.1 == some cappedRowsEndOfRow)
            (push 6 (fun _ => cappedRowsEndOfRow) (cappedRowsNext .read))
            (cappedRowsNext .restore)))
        (cappedRowsNext .finish)
  | .restore =>
    pop 0 cappedRowsObserve <|
      branch (fun r => r.1.isSome)
        (push 4 cappedRowsForward (cappedRowsNext .restore))
        (cappedRowsNext (.cell steinerUnaryCappedSumMachine.main))
  | .cell label => StackIndexEmbedding.statement cappedRowsSlots (cappedRowsInner (.cell label))
  | .emit =>
    pop 3 cappedRowsObserve <|
      branch (fun r => r.1.isSome)
        (push 6 cappedRowsForward (cappedRowsNext .emit))
        (cappedRowsNext .read)
  | .finish =>
    pop 6 cappedRowsObserve <|
      branch (fun r => r.1.isSome)
        (push 5 cappedRowsForward (cappedRowsNext .finish))
        (load (fun _ => cappedRowsInitial) halt)

/-- Run the capped-sum machine on each cell, accumulating one unary
answer per row and retaining even empty rows. -/
abbrev steinerUnaryCappedRowsMachine : FinTM2 where
  K := Fin 7
  k₀ := 5
  k₁ := 5
  Γ _ := SteinerUnaryCappedRowsSymbol
  Λ := CappedRowsLabel
  main := .read
  σ := CappedRowsRegister
  initialState := cappedRowsInitial
  m := cappedRowsProgram

private def cappedRowsCfg (label : Option CappedRowsLabel)
    (reversed value cell input output : List SteinerUnaryCappedRowsSymbol) : steinerUnaryCappedRowsMachine.Cfg where
  l := label
  var := cappedRowsInitial
  stk := ![reversed,[],[],value,cell,input,output]

private theorem cappedRows_update0 (a v c i o w : List SteinerUnaryCappedRowsSymbol) :
    Function.update (![a,[],[],v,c,i,o] : Fin 7 → List SteinerUnaryCappedRowsSymbol) 0 w = ![w,[],[],v,c,i,o] := by
  funext slot
  fin_cases slot <;> simp [Function.update]

private theorem cappedRows_update3 (a v c i o w : List SteinerUnaryCappedRowsSymbol) :
    Function.update (![a,[],[],v,c,i,o] : Fin 7 → List SteinerUnaryCappedRowsSymbol) 3 w = ![a,[],[],w,c,i,o] := by
  funext slot
  fin_cases slot <;> simp [Function.update]

private theorem cappedRows_update4 (a v c i o w : List SteinerUnaryCappedRowsSymbol) :
    Function.update (![a,[],[],v,c,i,o] : Fin 7 → List SteinerUnaryCappedRowsSymbol) 4 w = ![a,[],[],v,w,i,o] := by
  funext slot
  fin_cases slot <;> simp [Function.update]

private theorem cappedRows_update5 (a v c i o w : List SteinerUnaryCappedRowsSymbol) :
    Function.update (![a,[],[],v,c,i,o] : Fin 7 → List SteinerUnaryCappedRowsSymbol) 5 w = ![a,[],[],v,c,w,o] := by
  funext slot
  fin_cases slot <;> simp [Function.update]

private theorem cappedRows_update6 (a v c i o w : List SteinerUnaryCappedRowsSymbol) :
    Function.update (![a,[],[],v,c,i,o] : Fin 7 → List SteinerUnaryCappedRowsSymbol) 6 w = ![a,[],[],v,c,i,w] := by
  funext slot
  fin_cases slot <;> simp [Function.update]

private def cappedRows_one {a b : steinerUnaryCappedRowsMachine.Cfg}
    (move : steinerUnaryCappedRowsMachine.step a = some b) :
    EvalsToInTime steinerUnaryCappedRowsMachine.step a (some b) 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := move

private theorem cappedRows_readSymbol (symbol : Option Bool) (a i o : List SteinerUnaryCappedRowsSymbol) :
    steinerUnaryCappedRowsMachine.step (cappedRowsCfg (some .read) a [] [] (Sum.inr symbol::i) o) =
      some (cappedRowsCfg (some .read) (Sum.inr symbol::a) [] [] i o) := by
  simp [FinTM2.step,steinerUnaryCappedRowsMachine,cappedRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedRowsProgram,cappedRowsObserve,cappedRowsNext,cappedRowsForward,cappedRowsPayload,cappedRows_update0,cappedRows_update5]
  rfl

private theorem cappedRows_cellDelimiter (a i o : List SteinerUnaryCappedRowsSymbol) :
    steinerUnaryCappedRowsMachine.step (cappedRowsCfg (some .read) a [] [] (cappedRowsEndOfCell::i) o) =
      some (cappedRowsCfg (some .restore) a [] [] i o) := by
  simp [FinTM2.step,steinerUnaryCappedRowsMachine,cappedRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedRowsProgram,cappedRowsObserve,cappedRowsNext,cappedRowsPayload,cappedRowsEndOfCell,cappedRowsEndOfRow,cappedRows_update5]
  rfl

private def cappedRows_read (word : List (Option Bool)) (a i o : List SteinerUnaryCappedRowsSymbol) :
    EvalsToInTime steinerUnaryCappedRowsMachine.step
      (cappedRowsCfg (some .read) a [] [] (word.map Sum.inr++cappedRowsEndOfCell::i) o)
      (some (cappedRowsCfg (some .restore) ((word.map Sum.inr).reverse++a) [] [] i o)) (word.length+1) := by
  induction word generalizing a with
  | nil => exact cappedRows_one (cappedRows_cellDelimiter a i o)
  | cons symbol word ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _ (cappedRows_one (cappedRows_readSymbol symbol a
      (word.map Sum.inr++cappedRowsEndOfCell::i) o)) (ih (Sum.inr symbol::a))
    simpa only [List.map_cons,List.reverse_cons,List.length_cons,List.append_assoc,List.singleton_append,List.nil_append,List.cons_append]
      using all

private theorem cappedRows_restoreSymbol (symbol : SteinerUnaryCappedRowsSymbol)
    (a c i o : List SteinerUnaryCappedRowsSymbol) :
    steinerUnaryCappedRowsMachine.step (cappedRowsCfg (some .restore) (symbol::a) [] c i o) =
      some (cappedRowsCfg (some .restore) a [] (symbol::c) i o) := by
  simp [FinTM2.step,steinerUnaryCappedRowsMachine,cappedRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedRowsProgram,cappedRowsObserve,cappedRowsNext,cappedRowsForward,cappedRows_update0,cappedRows_update4]
  rfl

private theorem cappedRows_restoreEnd (c i o : List SteinerUnaryCappedRowsSymbol) :
    steinerUnaryCappedRowsMachine.step (cappedRowsCfg (some .restore) [] [] c i o) =
      some (cappedRowsCfg (some (.cell steinerUnaryCappedSumMachine.main)) [] [] c i o) := by
  simp [FinTM2.step,steinerUnaryCappedRowsMachine,cappedRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedRowsProgram,cappedRowsObserve,cappedRowsNext,cappedRows_update0]
  rfl

private def cappedRows_restore (a c i o : List SteinerUnaryCappedRowsSymbol) :
    EvalsToInTime steinerUnaryCappedRowsMachine.step (cappedRowsCfg (some .restore) a [] c i o)
      (some (cappedRowsCfg (some (.cell steinerUnaryCappedSumMachine.main)) [] [] (a.reverse++c) i o))
      (a.length+1) := by
  induction a generalizing c with
  | nil => exact cappedRows_one (cappedRows_restoreEnd c i o)
  | cons symbol a ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _
      (cappedRows_one (cappedRows_restoreSymbol symbol a c i o)) (ih (symbol::c))
    simpa only [List.reverse_cons,List.length_cons,List.append_assoc,List.singleton_append] using all

private def cappedRowsPassive (i o : List SteinerUnaryCappedRowsSymbol) (slot : Fin 7) : List SteinerUnaryCappedRowsSymbol :=
  if slot = 5 then i else if slot = 6 then o else []

private noncomputable def cappedRowsTranslated (i o : List SteinerUnaryCappedRowsSymbol)
    (c : steinerUnaryCappedSumMachine.Cfg) : steinerUnaryCappedRowsMachine.Cfg :=
  StackIndexEmbedding.configuration cappedRowsSlots (cappedRowsPassive i o)
    (cappedRowsTag.returningConfiguration .emit c)

private theorem cappedRows_cellStep (i o : List SteinerUnaryCappedRowsSymbol) {c after : steinerUnaryCappedSumMachine.Cfg}
    (move : steinerUnaryCappedSumMachine.step c = some after) :
    steinerUnaryCappedRowsMachine.step (cappedRowsTranslated i o c) = some (cappedRowsTranslated i o after) := by
  have tagged := cappedRowsTag.step_embedded_return .emit
    (base := steinerUnaryCappedSumMachine.m) (host := cappedRowsInner) (fun _ => rfl) move
  have framed := StackIndexEmbedding.step_on cappedRowsSlots (base := cappedRowsInner) (cappedRowsPassive i o)
    (cappedRowsTag.returningConfiguration .emit c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem cappedRows_cellTapes (i o : List SteinerUnaryCappedRowsSymbol) (word value : List (Option Bool))
    (c : steinerUnaryCappedSumMachine.Cfg) (tapes : c.stk = ![[],[],[],value,word]) :
    (cappedRowsTranslated i o c).stk = ![[],[],[],value.map Sum.inr,word.map Sum.inr,i,o] := by
  have image (slot : Fin 5) : (cappedRowsTranslated i o c).stk (cappedRowsSlots slot) =
      ((![[],[],[],value,word] : Fin 5 → List (Option Bool)) slot).map Sum.inr := by
    change StackIndexEmbedding.tapesAt cappedRowsSlots (fun k => (c.stk k).map Sum.inr)
      (cappedRowsPassive i o) (cappedRowsSlots slot) = _
    rw [StackIndexEmbedding.tapesAt_image,tapes]
  have extra (slot : Fin 7) (absent : ∀ j, cappedRowsSlots j ≠ slot) :
      (cappedRowsTranslated i o c).stk slot = cappedRowsPassive i o slot :=
    StackIndexEmbedding.tapesAt_extra cappedRowsSlots _ _ absent
  funext slot
  fin_cases slot
  · exact image 0
  · exact image 1
  · exact image 2
  · exact image 3
  · exact image 4
  · exact extra 5 (by intro j; fin_cases j <;> decide)
  · exact extra 6 (by intro j; fin_cases j <;> decide)

private theorem cappedRows_cellInit (i o : List SteinerUnaryCappedRowsSymbol) (word : List (Option Bool)) :
    cappedRowsTranslated i o (initList steinerUnaryCappedSumMachine word) =
      cappedRowsCfg (some (.cell steinerUnaryCappedSumMachine.main)) [] [] (word.map Sum.inr) i o := by
  apply congrArg (fun stk : Fin 7 → List SteinerUnaryCappedRowsSymbol =>
    (⟨some (.cell steinerUnaryCappedSumMachine.main),cappedRowsInitial,stk⟩ : steinerUnaryCappedRowsMachine.Cfg))
  apply cappedRows_cellTapes i o word [] (initList steinerUnaryCappedSumMachine word)
  funext slot
  fin_cases slot <;> rfl

private theorem cappedRows_cellReturn (i o : List SteinerUnaryCappedRowsSymbol) (value : List (Option Bool)) :
    cappedRowsTranslated i o (haltList steinerUnaryCappedSumMachine value) =
      cappedRowsCfg (some .emit) [] (value.map Sum.inr) [] i o := by
  apply congrArg (fun stk : Fin 7 → List SteinerUnaryCappedRowsSymbol =>
    (⟨some .emit,cappedRowsInitial,stk⟩ : steinerUnaryCappedRowsMachine.Cfg))
  apply cappedRows_cellTapes i o [] value (haltList steinerUnaryCappedSumMachine value)
  funext slot
  fin_cases slot <;> rfl

private def cappedRows_cell {time : ℕ} (i o : List SteinerUnaryCappedRowsSymbol) (word value : List (Option Bool))
    (run : TM2OutputsInTime steinerUnaryCappedSumMachine word (some value) time) :
    EvalsToInTime steinerUnaryCappedRowsMachine.step
      (cappedRowsCfg (some (.cell steinerUnaryCappedSumMachine.main)) [] [] (word.map Sum.inr) i o)
      (some (cappedRowsCfg (some .emit) [] (value.map Sum.inr) [] i o)) time := by
  refine ⟨⟨run.steps,?_⟩,run.steps_le_m⟩
  have all := iterate_map_some (cappedRowsTranslated i o) (fun move => cappedRows_cellStep i o move)
    run.steps run.evals_in_steps
  change (flip bind steinerUnaryCappedRowsMachine.step)^[run.steps]
    (some (cappedRowsTranslated i o (initList steinerUnaryCappedSumMachine word))) =
    some (cappedRowsTranslated i o (haltList steinerUnaryCappedSumMachine value)) at all
  rwa [cappedRows_cellInit,cappedRows_cellReturn] at all

private theorem cappedRows_emitSymbol (symbol : SteinerUnaryCappedRowsSymbol)
    (v i o : List SteinerUnaryCappedRowsSymbol) :
    steinerUnaryCappedRowsMachine.step (cappedRowsCfg (some .emit) [] (symbol::v) [] i o) =
      some (cappedRowsCfg (some .emit) [] v [] i (symbol::o)) := by
  simp [FinTM2.step,steinerUnaryCappedRowsMachine,cappedRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedRowsProgram,cappedRowsObserve,cappedRowsNext,cappedRowsForward,cappedRows_update3,cappedRows_update6]
  rfl

private theorem cappedRows_emitEnd (i o : List SteinerUnaryCappedRowsSymbol) :
    steinerUnaryCappedRowsMachine.step (cappedRowsCfg (some .emit) [] [] [] i o) =
      some (cappedRowsCfg (some .read) [] [] [] i o) := by
  simp [FinTM2.step,steinerUnaryCappedRowsMachine,cappedRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedRowsProgram,cappedRowsObserve,cappedRowsNext,cappedRows_update3]
  rfl

private def cappedRows_emit (v i o : List SteinerUnaryCappedRowsSymbol) :
    EvalsToInTime steinerUnaryCappedRowsMachine.step (cappedRowsCfg (some .emit) [] v [] i o)
      (some (cappedRowsCfg (some .read) [] [] [] i (v.reverse++o))) (v.length+1) := by
  induction v generalizing o with
  | nil => exact cappedRows_one (cappedRows_emitEnd i o)
  | cons symbol v ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _
      (cappedRows_one (cappedRows_emitSymbol symbol v i o)) (ih (symbol::o))
    simpa only [List.reverse_cons,List.length_cons,List.append_assoc,List.singleton_append] using all

private theorem cappedRows_rowDelimiter (i o : List SteinerUnaryCappedRowsSymbol) :
    steinerUnaryCappedRowsMachine.step (cappedRowsCfg (some .read) [] [] [] (cappedRowsEndOfRow::i) o) =
      some (cappedRowsCfg (some .read) [] [] [] i (cappedRowsEndOfRow::o)) := by
  simp [FinTM2.step,steinerUnaryCappedRowsMachine,cappedRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedRowsProgram,cappedRowsObserve,cappedRowsNext,cappedRowsEndOfRow,cappedRowsPayload,cappedRows_update5,cappedRows_update6]
  rfl

private theorem cappedRows_readEnd (o : List SteinerUnaryCappedRowsSymbol) :
    steinerUnaryCappedRowsMachine.step (cappedRowsCfg (some .read) [] [] [] [] o) =
      some (cappedRowsCfg (some .finish) [] [] [] [] o) := by
  simp [FinTM2.step,steinerUnaryCappedRowsMachine,cappedRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedRowsProgram,cappedRowsObserve,cappedRowsNext,cappedRows_update5]
  rfl

private theorem cappedRows_finishSymbol (symbol : SteinerUnaryCappedRowsSymbol) (i o : List SteinerUnaryCappedRowsSymbol) :
    steinerUnaryCappedRowsMachine.step (cappedRowsCfg (some .finish) [] [] [] i (symbol::o)) =
      some (cappedRowsCfg (some .finish) [] [] [] (symbol::i) o) := by
  simp [FinTM2.step,steinerUnaryCappedRowsMachine,cappedRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedRowsProgram,cappedRowsObserve,cappedRowsNext,cappedRowsForward,cappedRows_update5,cappedRows_update6]
  rfl

private theorem cappedRows_finishEnd (i : List SteinerUnaryCappedRowsSymbol) :
    steinerUnaryCappedRowsMachine.step (cappedRowsCfg (some .finish) [] [] [] i []) =
      some (cappedRowsCfg none [] [] [] i []) := by
  simp [FinTM2.step,steinerUnaryCappedRowsMachine,cappedRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedRowsProgram,cappedRowsObserve,cappedRows_update6]
  rfl

private def cappedRows_finish (i o : List SteinerUnaryCappedRowsSymbol) :
    EvalsToInTime steinerUnaryCappedRowsMachine.step (cappedRowsCfg (some .finish) [] [] [] i o)
      (some (cappedRowsCfg none [] [] [] (o.reverse++i) [])) (o.length+1) := by
  induction o generalizing i with
  | nil => exact cappedRows_one (cappedRows_finishEnd i)
  | cons symbol o ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _
      (cappedRows_one (cappedRows_finishSymbol symbol i o)) (ih (symbol::i))
    simpa only [List.reverse_cons,List.length_cons,List.append_assoc,List.singleton_append] using all

abbrev SteinerUnaryCappedRows := List (List SteinerUnaryCappedSumRequest)

private def cappedRowsCellFrame (request : SteinerUnaryCappedSumRequest) : List SteinerUnaryCappedRowsSymbol :=
  (encodeSteinerUnaryCappedSum request).map Sum.inr++[cappedRowsEndOfCell]

private def cappedRowsRowFrame (row : List SteinerUnaryCappedSumRequest) : List SteinerUnaryCappedRowsSymbol :=
  row.flatMap cappedRowsCellFrame

/-- Each cap, distance and prior weight is framed as one cell. Give
cells and rows distinct outer delimiters. -/
def encodeSteinerUnaryCappedRows (rows : SteinerUnaryCappedRows) : List SteinerUnaryCappedRowsSymbol :=
  rows.flatMap fun row => cappedRowsRowFrame row++[cappedRowsEndOfRow]

private def cappedRowsTallies (value : ℕ) : List SteinerUnaryCappedRowsSymbol := List.replicate value cappedRowsTally

/-- The row marker follows each unary total, including zero. -/
def encodeSteinerUnaryCappedRowTallies (totals : List ℕ) : List SteinerUnaryCappedRowsSymbol :=
  totals.flatMap fun total => cappedRowsTallies total++[cappedRowsEndOfRow]

/-- One sum of capped contributions per supplied row. -/
def steinerUnaryCappedRowsAnswer (rows : SteinerUnaryCappedRows) : List SteinerUnaryCappedRowsSymbol :=
  encodeSteinerUnaryCappedRowTallies (rows.map fun row => (row.map steinerUnaryCappedSum).sum)

private theorem cappedRowsCellFrame_length (request : SteinerUnaryCappedSumRequest) :
    (cappedRowsCellFrame request).length = (encodeSteinerUnaryCappedSum request).length+1 := by
  simp [cappedRowsCellFrame]

private theorem cappedRows_value_le (request : SteinerUnaryCappedSumRequest) :
    steinerUnaryCappedSum request ≤ (encodeSteinerUnaryCappedSum request).length := by
  rcases request with ⟨n,d,s⟩
  rw [encodeSteinerUnaryCappedSum_length]
  unfold steinerUnaryCappedSum
  dsimp only
  split_ifs <;> omega

private theorem cappedRows_taggedValue (request : SteinerUnaryCappedSumRequest) :
    (steinerUnaryCappedSumAnswer request).map Sum.inr = cappedRowsTallies (steinerUnaryCappedSum request) := by
  change (List.replicate (steinerUnaryCappedSum request) (some true)).map Sum.inr = _
  simp only [cappedRowsTallies,cappedRowsTally,List.map_replicate]

private def cappedRows_processCell (request : SteinerUnaryCappedSumRequest) (i o : List SteinerUnaryCappedRowsSymbol) :
    EvalsToInTime steinerUnaryCappedRowsMachine.step
      (cappedRowsCfg (some .read) [] [] [] (cappedRowsCellFrame request++i) o)
      (some (cappedRowsCfg (some .read) [] [] [] i (cappedRowsTallies (steinerUnaryCappedSum request)++o)))
      (8*(cappedRowsCellFrame request).length) := by
  let word := encodeSteinerUnaryCappedSum request
  let value := steinerUnaryCappedSumAnswer request
  have consumed := cappedRows_read word [] i o
  rw [List.append_nil] at consumed
  have placed := cappedRows_restore (word.map (Sum.inr : Option Bool → SteinerUnaryCappedRowsSymbol)).reverse [] i o
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse,List.length_map] at placed
  have loaded := EvalsToInTime.trans _ _ _ _ _ _ consumed placed
  have evaluated := cappedRows_cell i o word value (steinerUnaryCappedSumMachine_run request)
  have calculated := EvalsToInTime.trans _ _ _ _ _ _ loaded evaluated
  change EvalsToInTime steinerUnaryCappedRowsMachine.step _
    (some (cappedRowsCfg (some .emit) [] ((steinerUnaryCappedSumAnswer request).map Sum.inr) [] i o)) _ at calculated
  rw [cappedRows_taggedValue] at calculated
  have written := cappedRows_emit (value.map Sum.inr) i o
  change EvalsToInTime steinerUnaryCappedRowsMachine.step
    (cappedRowsCfg (some .emit) [] ((steinerUnaryCappedSumAnswer request).map Sum.inr) [] i o) _ _ at written
  rw [cappedRows_taggedValue] at written
  simp only [cappedRowsTallies,List.reverse_replicate,List.length_replicate] at written
  have all := EvalsToInTime.trans _ _ _ _ _ _ calculated written
  change EvalsToInTime _ (cappedRowsCfg (some .read) [] [] [] _ o) _ _
  simp only [cappedRowsCellFrame,List.append_assoc,List.singleton_append]
  refine ⟨all.toEvalsTo,?_⟩
  change all.steps ≤ 8*((word.map (Sum.inr : Option Bool → SteinerUnaryCappedRowsSymbol)++[cappedRowsEndOfCell]).length)
  simp only [List.length_append,List.length_map,List.length_singleton]
  have spent := all.steps_le_m
  have bound : steinerUnaryCappedSum request ≤ word.length := cappedRows_value_le request
  change all.steps ≤ (steinerUnaryCappedSum request+1)+((5*word.length+1)+((word.length+1)+(word.length+1))) at spent
  omega

private def cappedRows_processCells (row : List SteinerUnaryCappedSumRequest) (i o : List SteinerUnaryCappedRowsSymbol) :
    EvalsToInTime steinerUnaryCappedRowsMachine.step
      (cappedRowsCfg (some .read) [] [] [] (cappedRowsRowFrame row++i) o)
      (some (cappedRowsCfg (some .read) [] [] [] i (cappedRowsTallies ((row.map steinerUnaryCappedSum).sum)++o)))
      (8*(cappedRowsRowFrame row).length) := by
  induction row generalizing o with
  | nil => exact ⟨⟨0,rfl⟩,Nat.zero_le _⟩
  | cons request row ih =>
    have first := cappedRows_processCell request (cappedRowsRowFrame row++i) o
    have rest := ih (cappedRowsTallies (steinerUnaryCappedSum request)++o)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first rest
    have ordering :
        cappedRowsTallies ((row.map steinerUnaryCappedSum).sum)++(cappedRowsTallies (steinerUnaryCappedSum request)++o) =
          cappedRowsTallies (((request::row).map steinerUnaryCappedSum).sum)++o := by
      simp only [cappedRowsTallies,List.map_cons,List.sum_cons,Nat.add_comm (steinerUnaryCappedSum request),
        List.replicate_add,List.append_assoc]
    rw [ordering] at all
    change EvalsToInTime _ (cappedRowsCfg (some .read) [] [] [] _ o) _ _
    simp only [cappedRowsRowFrame,List.flatMap_cons,List.append_assoc,List.length_append]
    refine ⟨all.toEvalsTo,?_⟩
    have spent := all.steps_le_m
    change all.steps ≤ 8*(cappedRowsRowFrame row).length+8*(cappedRowsCellFrame request).length at spent
    change all.steps ≤ 8*((cappedRowsCellFrame request).length+(cappedRowsRowFrame row).length)
    omega

private theorem cappedRows_frame_cons (row : List SteinerUnaryCappedSumRequest) (rows : SteinerUnaryCappedRows) :
    encodeSteinerUnaryCappedRows (row::rows) =
      cappedRowsRowFrame row++cappedRowsEndOfRow::encodeSteinerUnaryCappedRows rows := by
  simp only [encodeSteinerUnaryCappedRows,List.flatMap_cons,List.append_assoc,List.singleton_append]

private theorem cappedRows_answer_cons (row : List SteinerUnaryCappedSumRequest) (rows : SteinerUnaryCappedRows) :
    steinerUnaryCappedRowsAnswer (row::rows) =
      cappedRowsTallies ((row.map steinerUnaryCappedSum).sum)++cappedRowsEndOfRow::steinerUnaryCappedRowsAnswer rows := by
  simp only [steinerUnaryCappedRowsAnswer,encodeSteinerUnaryCappedRowTallies,List.map_cons,List.flatMap_cons,
    List.append_assoc,List.singleton_append]

private def cappedRows_process (rows : SteinerUnaryCappedRows) (i o : List SteinerUnaryCappedRowsSymbol) :
    EvalsToInTime steinerUnaryCappedRowsMachine.step
      (cappedRowsCfg (some .read) [] [] [] (encodeSteinerUnaryCappedRows rows++i) o)
      (some (cappedRowsCfg (some .read) [] [] [] i ((steinerUnaryCappedRowsAnswer rows).reverse++o)))
      (8*(encodeSteinerUnaryCappedRows rows).length) := by
  induction rows generalizing o with
  | nil => exact ⟨⟨0,rfl⟩,Nat.zero_le _⟩
  | cons row rows ih =>
    let after := encodeSteinerUnaryCappedRows rows++i
    let tallies := cappedRowsTallies ((row.map steinerUnaryCappedSum).sum)
    have here := cappedRows_processCells row (cappedRowsEndOfRow::after) o
    have delimited := EvalsToInTime.trans _ _ _ _ _ _ here
      (cappedRows_one (cappedRows_rowDelimiter after (tallies++o)))
    have all := EvalsToInTime.trans _ _ _ _ _ _ delimited (ih (cappedRowsEndOfRow::(tallies++o)))
    rw [cappedRows_frame_cons,cappedRows_answer_cons]
    simp only [cappedRowsTallies,List.append_assoc,List.cons_append,List.reverse_append,List.reverse_cons,
      List.reverse_replicate,List.length_append,List.length_cons]
    refine ⟨all.toEvalsTo,?_⟩
    have spent := all.steps_le_m
    change all.steps ≤ 8*(encodeSteinerUnaryCappedRows rows).length+(1+8*(cappedRowsRowFrame row).length) at spent
    omega

private theorem cappedRows_rowSum_le_frame (row : List SteinerUnaryCappedSumRequest) :
    (row.map steinerUnaryCappedSum).sum ≤ (cappedRowsRowFrame row).length := by
  induction row with
  | nil => exact Nat.zero_le _
  | cons request row ih =>
    have each := cappedRows_value_le request
    change ((request::row).map steinerUnaryCappedSum).sum ≤
      (cappedRowsCellFrame request++cappedRowsRowFrame row).length
    simp only [List.map_cons,List.sum_cons,List.length_append,cappedRowsCellFrame_length]
    omega

theorem steinerUnaryCappedRowsAnswer_length_le (rows : SteinerUnaryCappedRows) :
    (steinerUnaryCappedRowsAnswer rows).length ≤ (encodeSteinerUnaryCappedRows rows).length := by
  induction rows with
  | nil => exact Nat.zero_le _
  | cons row rows ih =>
    rw [cappedRows_answer_cons,cappedRows_frame_cons]
    simp only [List.length_append,List.length_cons,cappedRowsTallies,List.length_replicate]
    have size := cappedRows_rowSum_le_frame row
    omega

private theorem cappedRows_init (word : List SteinerUnaryCappedRowsSymbol) :
    initList steinerUnaryCappedRowsMachine word = cappedRowsCfg (some .read) [] [] [] word [] := by
  apply congrArg (fun stk : Fin 7 → List SteinerUnaryCappedRowsSymbol =>
    (⟨some .read,cappedRowsInitial,stk⟩ : steinerUnaryCappedRowsMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem cappedRows_halt (word : List SteinerUnaryCappedRowsSymbol) :
    haltList steinerUnaryCappedRowsMachine word = cappedRowsCfg none [] [] [] word [] := by
  apply congrArg (fun stk : Fin 7 → List SteinerUnaryCappedRowsSymbol =>
    (⟨none,cappedRowsInitial,stk⟩ : steinerUnaryCappedRowsMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- Inspect each cell and sum the accepted contributions in its own
row. The transition bound is linear in the complete supplied frame. -/
def steinerUnaryCappedRowsMachine_run (rows : SteinerUnaryCappedRows) :
    let X := (encodeSteinerUnaryCappedRows rows).length
    TM2OutputsInTime steinerUnaryCappedRowsMachine (encodeSteinerUnaryCappedRows rows)
      (some (steinerUnaryCappedRowsAnswer rows)) (9*X+2) := by
  let out := steinerUnaryCappedRowsAnswer rows
  let X := (encodeSteinerUnaryCappedRows rows).length
  have processed := cappedRows_process rows [] []
  simp only [List.append_nil] at processed
  have read := EvalsToInTime.trans _ _ _ _ _ _ processed (cappedRows_one (cappedRows_readEnd out.reverse))
  have written := cappedRows_finish [] out.reverse
  rw [List.reverse_reverse,List.length_reverse,List.append_nil] at written
  have all := EvalsToInTime.trans _ _ _ _ _ _ read written
  change EvalsToInTime steinerUnaryCappedRowsMachine.step (initList _ _) (some (haltList _ _)) _
  rw [cappedRows_init,cappedRows_halt]
  refine ⟨all.toEvalsTo,?_⟩
  have spent := all.steps_le_m
  change all.steps ≤ out.length+1+(1+8*X) at spent
  change all.steps ≤ 9*X+2
  have length : out.length ≤ X := steinerUnaryCappedRowsAnswer_length_le rows
  omega

/-- The actual capped row machine has a linear input polynomial. -/
noncomputable def steinerUnaryCappedRowsMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryCappedRows id steinerUnaryCappedRowsAnswer where
  tm := steinerUnaryCappedRowsMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 9*Polynomial.X+Polynomial.C 2
  outputsFun rows := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_X,
      Polynomial.eval_C] using steinerUnaryCappedRowsMachine_run rows

open Finset

/-- Supply every vertex pair in root order. Each entry has the cap,
the distance for this transfer and its previously rooted weight. -/
def steinerForestTransferSumRows {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) : SteinerUnaryCappedRows :=
  List.ofFn fun (root : Fin n) => List.ofFn fun child => steinerForestTransferSumRequest dist h child root

theorem steinerUnaryCappedRowsAnswer_forestRound {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) :
    steinerUnaryCappedRowsAnswer (steinerForestTransferSumRows dist h) =
      encodeSteinerUnaryCappedRowTallies (inwardHeightWeightRounds dist (h+1)).toList := by
  unfold steinerUnaryCappedRowsAnswer steinerForestTransferSumRows
  rw [inwardHeightWeightRounds,Vector.toList_ofFn]
  rw [List.map_ofFn]
  apply congrArg encodeSteinerUnaryCappedRowTallies
  apply congrArg (@List.ofFn ℕ n)
  funext root
  simp only [Function.comp_apply,List.map_ofFn,List.sum_ofFn,steinerUnaryCappedSum,steinerForestTransferSumRequest]

private theorem cappedRows_rowFrame_length (row : List SteinerUnaryCappedSumRequest) :
    (cappedRowsRowFrame row).length = (row.map fun request => (encodeSteinerUnaryCappedSum request).length+1).sum := by
  simp only [cappedRowsRowFrame,List.length_flatMap,cappedRowsCellFrame_length]

private theorem cappedRows_frame_length (rows : SteinerUnaryCappedRows) :
    (encodeSteinerUnaryCappedRows rows).length = (rows.map fun row => (cappedRowsRowFrame row).length+1).sum := by
  simp only [encodeSteinerUnaryCappedRows,List.length_flatMap,List.length_append,
    List.length_singleton]

/-- For exact hop tables the supplied full frame is polynomial in n
at fixed depth, including the entries denoting unreachable pairs. -/
theorem encodeSteinerUnaryCappedRows_forestRound_length_le {n : ℕ} (G : Arcs (Fin n)) (dist : Fin n × Fin n → ℕ)
    (values : ∀ d, dist d = hops G d.1 d.2) (h : ℕ) :
    (encodeSteinerUnaryCappedRows (steinerForestTransferSumRows dist h)).length ≤
      n*(n*(2*n+inwardHeightWeightRoundBound n h+4)+1) := by
  let cap := 2*n+inwardHeightWeightRoundBound n h+4
  rw [cappedRows_frame_length,steinerForestTransferSumRows,List.map_ofFn,List.sum_ofFn]
  calc
    _ ≤ ∑ _ : Fin n, (n*cap+1) := by
      apply sum_le_sum
      intro root _
      apply Nat.succ_le_succ
      simp only [Function.comp_apply,cappedRows_rowFrame_length,List.map_ofFn,List.sum_ofFn]
      calc
        _ ≤ ∑ _ : Fin n, cap :=
          sum_le_sum fun child _ => Nat.succ_le_succ (encodeSteinerForestTransferSum_length_le G dist values h child root)
        _ = _ := by simp
    _ = _ := by simp [cap]

/-- With the full ordered cell frame supplied, every eligibility test
and every addition of the forest round is performed by the machine. -/
def steinerUnaryCappedRowsMachine_forestRound {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) :
    let input := encodeSteinerUnaryCappedRows (steinerForestTransferSumRows dist h)
    TM2OutputsInTime steinerUnaryCappedRowsMachine input
      (some (encodeSteinerUnaryCappedRowTallies (inwardHeightWeightRounds dist (h+1)).toList)) (9*input.length+2) := by
  simpa only [steinerUnaryCappedRowsAnswer_forestRound] using steinerUnaryCappedRowsMachine_run (steinerForestTransferSumRows dist h)

end OnlineReachabilityPreservers
