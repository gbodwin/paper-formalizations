import OnlineReachabilityPreservers.SteinerUnaryCappedRowsMachine

/-! Supply one unary cap for a complete matrix of transfer operands. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev SharedCapSymbol := SteinerUnaryCappedRowsSymbol
private abbrev SharedCapBaseLabel := steinerUnaryCappedRowsMachine.Λ
private abbrev SharedCapBaseRegister := steinerUnaryCappedRowsMachine.σ
private instance : Fintype SharedCapBaseLabel := steinerUnaryCappedRowsMachine.ΛFin

private inductive SharedCapLabel where
  | bound
  | read
  | copyCap
  | restoreCap
  | copyCell
  | clearCap
  | restoreFrame
  | evaluate (label : SharedCapBaseLabel)
  deriving Fintype

private abbrev SharedCapRegister := Option SharedCapSymbol × SharedCapBaseRegister
private abbrev SharedCapProgram := StackMachineTag.Program (Fin 7) SharedCapSymbol SharedCapLabel SharedCapRegister

private def sharedCapInitial : SharedCapRegister := (none,steinerUnaryCappedRowsMachine.initialState)

private def sharedCapObserve (_ : SharedCapRegister) (seen : Option SharedCapSymbol) : SharedCapRegister :=
  (seen,steinerUnaryCappedRowsMachine.initialState)

private def sharedCapNext (label : SharedCapLabel) : SharedCapProgram :=
  load (fun _ => sharedCapInitial) (goto (fun _ => label))

private def sharedCapTally : SharedCapSymbol := Sum.inr (some true)
private def sharedCapField : SharedCapSymbol := Sum.inr none
private def sharedCapEndCell : SharedCapSymbol := Sum.inl false
private def sharedCapEndRow : SharedCapSymbol := Sum.inl true

private def sharedCapSeen (r : SharedCapRegister) : SharedCapSymbol := r.1.getD sharedCapEndCell
private def sharedCapIgnore (r : SharedCapRegister) (_ : Option SharedCapSymbol) : SharedCapRegister := r

private def sharedCapTag :
    StackMachineTag SharedCapSymbol SharedCapSymbol SharedCapBaseLabel SharedCapLabel
      SharedCapBaseRegister SharedCapRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (none,r)
  readRegister := Prod.snd
  writeLabel := .evaluate
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def sharedCapProgram : SharedCapLabel → SharedCapProgram
  | .bound =>
    pop 5 sharedCapObserve <|
      branch (fun r => r.1 == some sharedCapTally)
        (push 4 (fun _ => sharedCapTally) (sharedCapNext .bound))
        (sharedCapNext .read)
  | .read =>
    peek 5 sharedCapObserve <|
      branch (fun r => r.1.isSome)
        (branch (fun r => r.1 == some sharedCapEndRow)
          (pop 5 sharedCapIgnore <|
            push 6 (fun _ => sharedCapEndRow) (sharedCapNext .read))
          (sharedCapNext .copyCap))
        (sharedCapNext .clearCap)
  | .copyCap =>
    pop 4 sharedCapObserve <|
      branch (fun r => r.1.isSome)
        (push 0 (fun _ => sharedCapTally) <|
          push 6 (fun _ => sharedCapTally) (sharedCapNext .copyCap))
        (push 6 (fun _ => sharedCapField) (sharedCapNext .restoreCap))
  | .restoreCap =>
    pop 0 sharedCapObserve <|
      branch (fun r => r.1.isSome)
        (push 4 (fun _ => sharedCapTally) (sharedCapNext .restoreCap))
        (sharedCapNext .copyCell)
  | .copyCell =>
    pop 5 sharedCapObserve <|
      push 6 sharedCapSeen <|
        branch (fun r => r.1 == some sharedCapEndCell)
          (sharedCapNext .read) (sharedCapNext .copyCell)
  | .clearCap =>
    pop 4 sharedCapObserve <|
      branch (fun r => r.1.isSome) (sharedCapNext .clearCap) (sharedCapNext .restoreFrame)
  | .restoreFrame =>
    pop 6 sharedCapObserve <|
      branch (fun r => r.1.isSome)
        (push 5 sharedCapSeen (sharedCapNext .restoreFrame))
        (sharedCapNext (.evaluate steinerUnaryCappedRowsMachine.main))
  | .evaluate l => sharedCapTag.statement (steinerUnaryCappedRowsMachine.m l)

/-- Copy the same bound into every cell and start the checked row
machine with the expanded frame already on its initial stack. -/
abbrev steinerUnarySharedCapRowsMachine : FinTM2 where
  K := Fin 7
  k₀ := 5
  k₁ := 5
  Γ _ := SharedCapSymbol
  Λ := SharedCapLabel
  main := .bound
  σ := SharedCapRegister
  initialState := sharedCapInitial
  m := sharedCapProgram

private def sharedCapCfg (label : Option SharedCapLabel) (backup cap input output : List SharedCapSymbol) :
    steinerUnarySharedCapRowsMachine.Cfg where
  l := label
  var := sharedCapInitial
  stk := ![backup,[],[],[],cap,input,output]

private theorem sharedCap_update0 (a b i o w : List SharedCapSymbol) :
    Function.update (![a,[],[],[],b,i,o] : Fin 7 → List SharedCapSymbol) 0 w = ![w,[],[],[],b,i,o] := by
  funext x
  fin_cases x <;> simp [Function.update]

private theorem sharedCap_update4 (a b i o w : List SharedCapSymbol) :
    Function.update (![a,[],[],[],b,i,o] : Fin 7 → List SharedCapSymbol) 4 w = ![a,[],[],[],w,i,o] := by
  funext x
  fin_cases x <;> simp [Function.update]

private theorem sharedCap_update5 (a b i o w : List SharedCapSymbol) :
    Function.update (![a,[],[],[],b,i,o] : Fin 7 → List SharedCapSymbol) 5 w = ![a,[],[],[],b,w,o] := by
  funext x
  fin_cases x <;> simp [Function.update]

private theorem sharedCap_update6 (a b i o w : List SharedCapSymbol) :
    Function.update (![a,[],[],[],b,i,o] : Fin 7 → List SharedCapSymbol) 6 w = ![a,[],[],[],b,i,w] := by
  funext x
  fin_cases x <;> simp [Function.update]

private def sharedCap_one {a b : steinerUnarySharedCapRowsMachine.Cfg}
    (move : steinerUnarySharedCapRowsMachine.step a = some b) :
    EvalsToInTime steinerUnarySharedCapRowsMachine.step a (some b) 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := move

private def sharedCapTallies (n : ℕ) : List SharedCapSymbol := List.replicate n sharedCapTally

private theorem sharedCapTallies_push (n : ℕ) (tail : List SharedCapSymbol) :
    sharedCapTallies n++sharedCapTally::tail = sharedCapTallies (n+1)++tail := by
  simp only [sharedCapTallies,List.replicate_add,List.replicate_one,List.append_assoc,List.singleton_append]

private theorem sharedCap_boundTally (cap input : List SharedCapSymbol) :
    steinerUnarySharedCapRowsMachine.step (sharedCapCfg (some .bound) [] cap (sharedCapTally::input) []) =
      some (sharedCapCfg (some .bound) [] (sharedCapTally::cap) input []) := by
  simp [FinTM2.step,steinerUnarySharedCapRowsMachine,sharedCapCfg,Turing.TM2.step,Turing.TM2.stepAux,
    sharedCapProgram,sharedCapObserve,sharedCapNext,sharedCap_update4,sharedCap_update5]
  rfl

private theorem sharedCap_boundEnd (cap input : List SharedCapSymbol) :
    steinerUnarySharedCapRowsMachine.step (sharedCapCfg (some .bound) [] cap (sharedCapEndCell::input) []) =
      some (sharedCapCfg (some .read) [] cap input []) := by
  simp [FinTM2.step,steinerUnarySharedCapRowsMachine,sharedCapCfg,Turing.TM2.step,Turing.TM2.stepAux,
    sharedCapProgram,sharedCapObserve,sharedCapNext,sharedCapTally,sharedCapEndCell,sharedCap_update5]
  rfl

private def sharedCap_bound (n : ℕ) (cap input : List SharedCapSymbol) :
    EvalsToInTime steinerUnarySharedCapRowsMachine.step
      (sharedCapCfg (some .bound) [] cap (sharedCapTallies n++sharedCapEndCell::input) [])
      (some (sharedCapCfg (some .read) [] (sharedCapTallies n++cap) input [])) (n+1) := by
  induction n generalizing cap with
  | zero => exact sharedCap_one (sharedCap_boundEnd cap input)
  | succ n ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _ (sharedCap_one (sharedCap_boundTally cap
      (sharedCapTallies n++sharedCapEndCell::input))) (ih (sharedCapTally::cap))
    rw [sharedCapTallies_push] at all
    exact all

private theorem sharedCap_startCell (symbol : Option Bool) (cap input output : List SharedCapSymbol) :
    steinerUnarySharedCapRowsMachine.step (sharedCapCfg (some .read) [] cap (Sum.inr symbol::input) output) =
      some (sharedCapCfg (some .copyCap) [] cap (Sum.inr symbol::input) output) := by
  simp [FinTM2.step,steinerUnarySharedCapRowsMachine,sharedCapCfg,Turing.TM2.step,Turing.TM2.stepAux,
    sharedCapProgram,sharedCapObserve,sharedCapNext,sharedCapEndRow]
  rfl

private theorem sharedCap_copyTally (a cap input output : List SharedCapSymbol) :
    steinerUnarySharedCapRowsMachine.step (sharedCapCfg (some .copyCap) a (sharedCapTally::cap) input output) =
      some (sharedCapCfg (some .copyCap) (sharedCapTally::a) cap input (sharedCapTally::output)) := by
  simp [FinTM2.step,steinerUnarySharedCapRowsMachine,sharedCapCfg,Turing.TM2.step,Turing.TM2.stepAux,
    sharedCapProgram,sharedCapObserve,sharedCapNext,sharedCap_update0,sharedCap_update4,sharedCap_update6]
  rfl

private theorem sharedCap_copyEnd (a input output : List SharedCapSymbol) :
    steinerUnarySharedCapRowsMachine.step (sharedCapCfg (some .copyCap) a [] input output) =
      some (sharedCapCfg (some .restoreCap) a [] input (sharedCapField::output)) := by
  simp [FinTM2.step,steinerUnarySharedCapRowsMachine,sharedCapCfg,Turing.TM2.step,Turing.TM2.stepAux,
    sharedCapProgram,sharedCapObserve,sharedCapNext,sharedCap_update4,sharedCap_update6]
  rfl

private def sharedCap_copy (n : ℕ) (a input output : List SharedCapSymbol) :
    EvalsToInTime steinerUnarySharedCapRowsMachine.step
      (sharedCapCfg (some .copyCap) a (sharedCapTallies n) input output)
      (some (sharedCapCfg (some .restoreCap) (sharedCapTallies n++a) [] input
        (sharedCapField::(sharedCapTallies n++output)))) (n+1) := by
  induction n generalizing a output with
  | zero => exact sharedCap_one (sharedCap_copyEnd a input output)
  | succ n ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _ (sharedCap_one (sharedCap_copyTally a (sharedCapTallies n) input output))
      (ih (sharedCapTally::a) (sharedCapTally::output))
    rw [sharedCapTallies_push,sharedCapTallies_push] at all
    exact all

private theorem sharedCap_restoreTally (a cap input output : List SharedCapSymbol) :
    steinerUnarySharedCapRowsMachine.step (sharedCapCfg (some .restoreCap) (sharedCapTally::a) cap input output) =
      some (sharedCapCfg (some .restoreCap) a (sharedCapTally::cap) input output) := by
  simp [FinTM2.step,steinerUnarySharedCapRowsMachine,sharedCapCfg,Turing.TM2.step,Turing.TM2.stepAux,
    sharedCapProgram,sharedCapObserve,sharedCapNext,sharedCap_update0,sharedCap_update4]
  rfl

private theorem sharedCap_restoreEnd (cap input output : List SharedCapSymbol) :
    steinerUnarySharedCapRowsMachine.step (sharedCapCfg (some .restoreCap) [] cap input output) =
      some (sharedCapCfg (some .copyCell) [] cap input output) := by
  simp [FinTM2.step,steinerUnarySharedCapRowsMachine,sharedCapCfg,Turing.TM2.step,Turing.TM2.stepAux,
    sharedCapProgram,sharedCapObserve,sharedCapNext,sharedCap_update0]
  rfl

private def sharedCap_restore (n : ℕ) (cap input output : List SharedCapSymbol) :
    EvalsToInTime steinerUnarySharedCapRowsMachine.step
      (sharedCapCfg (some .restoreCap) (sharedCapTallies n) cap input output)
      (some (sharedCapCfg (some .copyCell) [] (sharedCapTallies n++cap) input output)) (n+1) := by
  induction n generalizing cap with
  | zero => exact sharedCap_one (sharedCap_restoreEnd cap input output)
  | succ n ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _
      (sharedCap_one (sharedCap_restoreTally (sharedCapTallies n) cap input output)) (ih (sharedCapTally::cap))
    rw [sharedCapTallies_push] at all
    exact all

private theorem sharedCap_cellSymbol (symbol : Option Bool) (cap input output : List SharedCapSymbol) :
    steinerUnarySharedCapRowsMachine.step (sharedCapCfg (some .copyCell) [] cap (Sum.inr symbol::input) output) =
      some (sharedCapCfg (some .copyCell) [] cap input (Sum.inr symbol::output)) := by
  simp [FinTM2.step,steinerUnarySharedCapRowsMachine,sharedCapCfg,Turing.TM2.step,Turing.TM2.stepAux,
    sharedCapProgram,sharedCapObserve,sharedCapNext,sharedCapSeen,sharedCapEndCell,sharedCap_update5,sharedCap_update6]
  rfl

private theorem sharedCap_cellEnd (cap input output : List SharedCapSymbol) :
    steinerUnarySharedCapRowsMachine.step (sharedCapCfg (some .copyCell) [] cap (sharedCapEndCell::input) output) =
      some (sharedCapCfg (some .read) [] cap input (sharedCapEndCell::output)) := by
  simp [FinTM2.step,steinerUnarySharedCapRowsMachine,sharedCapCfg,Turing.TM2.step,Turing.TM2.stepAux,
    sharedCapProgram,sharedCapObserve,sharedCapNext,sharedCapSeen,sharedCap_update5,sharedCap_update6]
  rfl

private def sharedCap_cell (word : List (Option Bool)) (cap input output : List SharedCapSymbol) :
    EvalsToInTime steinerUnarySharedCapRowsMachine.step
      (sharedCapCfg (some .copyCell) [] cap (word.map Sum.inr++sharedCapEndCell::input) output)
      (some (sharedCapCfg (some .read) [] cap input (sharedCapEndCell::((word.map Sum.inr).reverse++output))))
      (word.length+1) := by
  induction word generalizing output with
  | nil => exact sharedCap_one (sharedCap_cellEnd cap input output)
  | cons symbol word ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _
      (sharedCap_one (sharedCap_cellSymbol symbol cap (word.map Sum.inr++sharedCapEndCell::input) output))
      (ih (Sum.inr symbol::output))
    simpa only [List.map_cons,List.reverse_cons,List.length_cons,List.append_assoc,List.singleton_append,
      List.nil_append,List.cons_append] using all

private theorem sharedCap_rowEnd (cap input output : List SharedCapSymbol) :
    steinerUnarySharedCapRowsMachine.step (sharedCapCfg (some .read) [] cap (sharedCapEndRow::input) output) =
      some (sharedCapCfg (some .read) [] cap input (sharedCapEndRow::output)) := by
  simp [FinTM2.step,steinerUnarySharedCapRowsMachine,sharedCapCfg,Turing.TM2.step,Turing.TM2.stepAux,
    sharedCapProgram,sharedCapObserve,sharedCapNext,sharedCap_update5,sharedCap_update6]
  rfl

private theorem sharedCap_inputEnd (cap output : List SharedCapSymbol) :
    steinerUnarySharedCapRowsMachine.step (sharedCapCfg (some .read) [] cap [] output) =
      some (sharedCapCfg (some .clearCap) [] cap [] output) := by
  simp [FinTM2.step,steinerUnarySharedCapRowsMachine,sharedCapCfg,Turing.TM2.step,Turing.TM2.stepAux,
    sharedCapProgram,sharedCapObserve,sharedCapNext]
  rfl

private theorem sharedCap_clearTally (word output : List SharedCapSymbol) :
    steinerUnarySharedCapRowsMachine.step (sharedCapCfg (some .clearCap) [] (sharedCapTally::word) [] output) =
      some (sharedCapCfg (some .clearCap) [] word [] output) := by
  simp [FinTM2.step,steinerUnarySharedCapRowsMachine,sharedCapCfg,Turing.TM2.step,Turing.TM2.stepAux,
    sharedCapProgram,sharedCapObserve,sharedCapNext,sharedCap_update4]
  rfl

private theorem sharedCap_clearEnd (output : List SharedCapSymbol) :
    steinerUnarySharedCapRowsMachine.step (sharedCapCfg (some .clearCap) [] [] [] output) =
      some (sharedCapCfg (some .restoreFrame) [] [] [] output) := by
  simp [FinTM2.step,steinerUnarySharedCapRowsMachine,sharedCapCfg,Turing.TM2.step,Turing.TM2.stepAux,
    sharedCapProgram,sharedCapObserve,sharedCapNext,sharedCap_update4]
  rfl

private def sharedCap_clear (n : ℕ) (output : List SharedCapSymbol) :
    EvalsToInTime steinerUnarySharedCapRowsMachine.step
      (sharedCapCfg (some .clearCap) [] (sharedCapTallies n) [] output)
      (some (sharedCapCfg (some .restoreFrame) [] [] [] output)) (n+1) := by
  induction n with
  | zero => exact sharedCap_one (sharedCap_clearEnd output)
  | succ n ih =>
    exact EvalsToInTime.trans _ _ _ _ _ _ (sharedCap_one (sharedCap_clearTally (sharedCapTallies n) output)) ih

private theorem sharedCap_frameSymbol (symbol : SharedCapSymbol) (input output : List SharedCapSymbol) :
    steinerUnarySharedCapRowsMachine.step (sharedCapCfg (some .restoreFrame) [] [] input (symbol::output)) =
      some (sharedCapCfg (some .restoreFrame) [] [] (symbol::input) output) := by
  simp [FinTM2.step,steinerUnarySharedCapRowsMachine,sharedCapCfg,Turing.TM2.step,Turing.TM2.stepAux,
    sharedCapProgram,sharedCapObserve,sharedCapNext,sharedCapSeen,sharedCap_update5,sharedCap_update6]
  rfl

private theorem sharedCap_frameEnd (input : List SharedCapSymbol) :
    steinerUnarySharedCapRowsMachine.step (sharedCapCfg (some .restoreFrame) [] [] input []) =
      some (sharedCapCfg (some (.evaluate steinerUnaryCappedRowsMachine.main)) [] [] input []) := by
  simp [FinTM2.step,steinerUnarySharedCapRowsMachine,sharedCapCfg,Turing.TM2.step,Turing.TM2.stepAux,
    sharedCapProgram,sharedCapObserve,sharedCapNext,sharedCap_update6]
  rfl

private def sharedCap_restoreFrame (input output : List SharedCapSymbol) :
    EvalsToInTime steinerUnarySharedCapRowsMachine.step (sharedCapCfg (some .restoreFrame) [] [] input output)
      (some (sharedCapCfg (some (.evaluate steinerUnaryCappedRowsMachine.main)) [] [] (output.reverse++input) []))
      (output.length+1) := by
  induction output generalizing input with
  | nil => exact sharedCap_one (sharedCap_frameEnd input)
  | cons symbol output ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _
      (sharedCap_one (sharedCap_frameSymbol symbol input output)) (ih (symbol::input))
    simpa only [List.reverse_cons,List.length_cons,List.append_assoc,List.singleton_append] using all

abbrev SteinerUnarySharedCapRows := ℕ × List (List (ℕ × ℕ))

private def sharedCapPayload (cell : ℕ × ℕ) : List (Option Bool) :=
  List.replicate cell.1 (some true)++none::List.replicate cell.2 (some true)

private def sharedCapRawCell (cell : ℕ × ℕ) : List SharedCapSymbol :=
  (sharedCapPayload cell).map Sum.inr++[sharedCapEndCell]

private def sharedCapRawRow (row : List (ℕ × ℕ)) : List SharedCapSymbol := row.flatMap sharedCapRawCell

private def sharedCapRawRows (rows : List (List (ℕ × ℕ))) : List SharedCapSymbol :=
  rows.flatMap fun row => sharedCapRawRow row++[sharedCapEndRow]

/-- One unary bound followed by rows of distances and prior weights. -/
def encodeSteinerUnarySharedCapRows (request : SteinerUnarySharedCapRows) : List SteinerUnaryCappedRowsSymbol :=
  sharedCapTallies request.1++sharedCapEndCell::sharedCapRawRows request.2

/-- The row evaluator receives the same cap for every pair. -/
def steinerUnarySharedCapExpanded (request : SteinerUnarySharedCapRows) : SteinerUnaryCappedRows :=
  request.2.map fun row => row.map fun cell => (request.1,cell.1,cell.2)

/-- Compute the row totals with the shared cap. -/
def steinerUnarySharedCapRowsAnswer (request : SteinerUnarySharedCapRows) : List SteinerUnaryCappedRowsSymbol :=
  steinerUnaryCappedRowsAnswer (steinerUnarySharedCapExpanded request)

private def sharedCapFullCell (n : ℕ) (cell : ℕ × ℕ) : List SharedCapSymbol :=
  sharedCapTallies n++sharedCapField::sharedCapRawCell cell

private def sharedCapFullRow (n : ℕ) (row : List (ℕ × ℕ)) : List SharedCapSymbol :=
  row.flatMap (sharedCapFullCell n)

private theorem sharedCapFullCell_eq (n : ℕ) (cell : ℕ × ℕ) :
    sharedCapFullCell n cell = (encodeSteinerUnaryCappedSum (n,cell.1,cell.2)).map Sum.inr++[sharedCapEndCell] := by
  change _ = (List.replicate n (some true)++none::sharedCapPayload cell).map Sum.inr++[sharedCapEndCell]
  simp only [sharedCapFullCell,sharedCapTallies,sharedCapRawCell,sharedCapField,sharedCapTally,
    List.map_append,List.map_replicate,List.map_cons,List.append_assoc,List.cons_append]

private theorem sharedCap_expanded_cons (n : ℕ) (row : List (ℕ × ℕ)) (rows : List (List (ℕ × ℕ))) :
    encodeSteinerUnaryCappedRows (steinerUnarySharedCapExpanded (n,row::rows)) =
      sharedCapFullRow n row++sharedCapEndRow::encodeSteinerUnaryCappedRows (steinerUnarySharedCapExpanded (n,rows)) := by
  let cells := fun request : SteinerUnaryCappedSumRequest =>
    (encodeSteinerUnaryCappedSum request).map (Sum.inr : Option Bool → SharedCapSymbol)++[sharedCapEndCell]
  change ((row.map fun cell => (n,cell.1,cell.2)).flatMap cells++[sharedCapEndRow])++
      encodeSteinerUnaryCappedRows (steinerUnarySharedCapExpanded (n,rows)) = _
  have same : (fun cell : ℕ × ℕ => cells (n,cell.1,cell.2)) = sharedCapFullCell n :=
    funext fun cell => (sharedCapFullCell_eq n cell).symm
  simp only [sharedCapFullRow,List.flatMap_map,List.append_assoc,List.singleton_append]
  rw [same]

private theorem sharedCapRawCell_length (cell : ℕ × ℕ) :
    (sharedCapRawCell cell).length = (sharedCapPayload cell).length+1 := by
  simp [sharedCapRawCell]

private theorem sharedCapFullCell_length (n : ℕ) (cell : ℕ × ℕ) :
    (sharedCapFullCell n cell).length = n+1+(sharedCapRawCell cell).length := by
  simp only [sharedCapFullCell,sharedCapTallies,List.length_append,List.length_replicate,List.length_cons]
  omega

private def sharedCap_processCell (n : ℕ) (cell : ℕ × ℕ) (input output : List SharedCapSymbol) :
    EvalsToInTime steinerUnarySharedCapRowsMachine.step
      (sharedCapCfg (some .read) [] (sharedCapTallies n) (sharedCapRawCell cell++input) output)
      (some (sharedCapCfg (some .read) [] (sharedCapTallies n) input ((sharedCapFullCell n cell).reverse++output)))
      (2*(sharedCapFullCell n cell).length) := by
  let word := sharedCapPayload cell
  let i := word.map (Sum.inr : Option Bool → SharedCapSymbol)++sharedCapEndCell::input
  have present : word ≠ [] := by
    intro empty
    have count := congrArg List.length empty
    simp only [word,sharedCapPayload,List.length_append,List.length_replicate,List.length_cons,List.length_nil] at count
    omega
  have first : EvalsToInTime steinerUnarySharedCapRowsMachine.step
      (sharedCapCfg (some .read) [] (sharedCapTallies n) i output)
      (some (sharedCapCfg (some .copyCap) [] (sharedCapTallies n) i output)) 1 := by
    cases wordEq : word with
    | nil => exact False.elim (present wordEq)
    | cons symbol tail =>
      have exactInput : i = Sum.inr symbol::(tail.map Sum.inr++sharedCapEndCell::input) := by
        simp only [i,wordEq,List.map_cons,List.cons_append]
      rw [exactInput]
      exact sharedCap_one (sharedCap_startCell symbol _ _ _)
  have copied := sharedCap_copy n [] i output
  rw [List.append_nil] at copied
  have expanded := EvalsToInTime.trans _ _ _ _ _ _ first copied
  have returned := sharedCap_restore n [] i (sharedCapField::(sharedCapTallies n++output))
  rw [List.append_nil] at returned
  have ready := EvalsToInTime.trans _ _ _ _ _ _ expanded returned
  have transferred := sharedCap_cell word (sharedCapTallies n) input (sharedCapField::(sharedCapTallies n++output))
  have all := EvalsToInTime.trans _ _ _ _ _ _ ready transferred
  have source : sharedCapRawCell cell++input = i := by
    simp only [i,word,sharedCapRawCell,List.append_assoc,List.singleton_append]
  have target : (sharedCapFullCell n cell).reverse++output =
      sharedCapEndCell::((word.map Sum.inr).reverse++sharedCapField::(sharedCapTallies n++output)) := by
    simp only [sharedCapFullCell,sharedCapRawCell,word,List.reverse_append,List.reverse_cons,List.reverse_nil,
      sharedCapTallies,List.reverse_replicate,List.append_assoc,List.nil_append,List.cons_append]
  rw [source,target,sharedCapFullCell_length,sharedCapRawCell_length]
  refine ⟨all.toEvalsTo,?_⟩
  have spent := all.steps_le_m
  change all.steps ≤ word.length+1+(n+1+(n+1+1)) at spent
  change all.steps ≤ 2*(n+1+(word.length+1))
  omega

private def sharedCap_processRow (n : ℕ) (row : List (ℕ × ℕ)) (input output : List SharedCapSymbol) :
    EvalsToInTime steinerUnarySharedCapRowsMachine.step
      (sharedCapCfg (some .read) [] (sharedCapTallies n) (sharedCapRawRow row++input) output)
      (some (sharedCapCfg (some .read) [] (sharedCapTallies n) input ((sharedCapFullRow n row).reverse++output)))
      (2*(sharedCapFullRow n row).length) := by
  induction row generalizing output with
  | nil => exact ⟨⟨0,rfl⟩,Nat.zero_le _⟩
  | cons cell row ih =>
    have first := sharedCap_processCell n cell (sharedCapRawRow row++input) output
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih ((sharedCapFullCell n cell).reverse++output))
    change EvalsToInTime _ (sharedCapCfg (some .read) [] (sharedCapTallies n) _ output) _ _
    simp only [sharedCapRawRow,sharedCapFullRow,List.flatMap_cons,List.reverse_append,List.append_assoc,List.length_append]
    refine ⟨all.toEvalsTo,?_⟩
    have spent := all.steps_le_m
    change all.steps ≤ 2*(sharedCapFullRow n row).length+2*(sharedCapFullCell n cell).length at spent
    change all.steps ≤ 2*((sharedCapFullCell n cell).length+(sharedCapFullRow n row).length)
    omega

private theorem sharedCapRawRows_cons (row : List (ℕ × ℕ)) (rows : List (List (ℕ × ℕ))) :
    sharedCapRawRows (row::rows) = sharedCapRawRow row++sharedCapEndRow::sharedCapRawRows rows := by
  simp only [sharedCapRawRows,List.flatMap_cons,List.append_assoc,List.singleton_append]

private def sharedCap_processRows (n : ℕ) (rows : List (List (ℕ × ℕ))) (input output : List SharedCapSymbol) :
    let frame := encodeSteinerUnaryCappedRows (steinerUnarySharedCapExpanded (n,rows))
    EvalsToInTime steinerUnarySharedCapRowsMachine.step
      (sharedCapCfg (some .read) [] (sharedCapTallies n) (sharedCapRawRows rows++input) output)
      (some (sharedCapCfg (some .read) [] (sharedCapTallies n) input (frame.reverse++output)))
      (2*frame.length) := by
  induction rows generalizing output with
  | nil => exact ⟨⟨0,rfl⟩,Nat.zero_le _⟩
  | cons row rows ih =>
    let after := sharedCapRawRows rows++input
    have first := sharedCap_processRow n row (sharedCapEndRow::after) output
    have marked := EvalsToInTime.trans _ _ _ _ _ _ first
      (sharedCap_one (sharedCap_rowEnd (sharedCapTallies n) after ((sharedCapFullRow n row).reverse++output)))
    have all := EvalsToInTime.trans _ _ _ _ _ _ marked (ih (sharedCapEndRow::((sharedCapFullRow n row).reverse++output)))
    dsimp only
    rw [sharedCapRawRows_cons,sharedCap_expanded_cons]
    simp only [List.append_assoc,List.cons_append,List.reverse_append,List.reverse_cons,List.length_append,List.length_cons]
    refine ⟨all.toEvalsTo,?_⟩
    have spent := all.steps_le_m
    change all.steps ≤ 2*(encodeSteinerUnaryCappedRows (steinerUnarySharedCapExpanded (n,rows))).length+
      (1+2*(sharedCapFullRow n row).length) at spent
    omega

private theorem sharedCap_fullCell_length_le (n : ℕ) (cell : ℕ × ℕ) :
    (sharedCapFullCell n cell).length ≤ (n+2)*(sharedCapRawCell cell).length := by
  have positive : 1 ≤ (sharedCapRawCell cell).length := by rw [sharedCapRawCell_length]; omega
  rw [sharedCapFullCell_length]
  calc
    _ ≤ (n+1)*(sharedCapRawCell cell).length+(sharedCapRawCell cell).length := by
      have multiplied := Nat.mul_le_mul_left (n+1) positive
      rw [Nat.mul_one] at multiplied
      exact Nat.add_le_add_right multiplied _
    _ = _ := by ring

private theorem sharedCap_fullRow_length_le (n : ℕ) (row : List (ℕ × ℕ)) :
    (sharedCapFullRow n row).length ≤ (n+2)*(sharedCapRawRow row).length := by
  induction row with
  | nil => exact Nat.zero_le _
  | cons cell row ih =>
    change (sharedCapFullCell n cell++sharedCapFullRow n row).length ≤
      (n+2)*(sharedCapRawCell cell++sharedCapRawRow row).length
    rw [List.length_append,List.length_append,Nat.mul_add]
    exact Nat.add_le_add (sharedCap_fullCell_length_le n cell) ih

private theorem sharedCap_fullFrame_length_le (n : ℕ) (rows : List (List (ℕ × ℕ))) :
    (encodeSteinerUnaryCappedRows (steinerUnarySharedCapExpanded (n,rows))).length ≤ (n+2)*(sharedCapRawRows rows).length := by
  induction rows with
  | nil => exact Nat.zero_le _
  | cons row rows ih =>
    rw [sharedCap_expanded_cons,sharedCapRawRows_cons]
    simp only [List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
    have mark : 1 ≤ n+2 := by omega
    have both := Nat.add_le_add (sharedCap_fullRow_length_le n row) (Nat.add_le_add ih mark)
    exact both

private theorem sharedCap_input_length (request : SteinerUnarySharedCapRows) :
    (encodeSteinerUnarySharedCapRows request).length = request.1+1+(sharedCapRawRows request.2).length := by
  simp only [encodeSteinerUnarySharedCapRows,sharedCapTallies,List.length_append,List.length_replicate,List.length_cons]
  omega

/-- The full frame can repeat a cap of n symbols once per input cell. -/
theorem encodeSteinerUnarySharedCapExpanded_length_le (request : SteinerUnarySharedCapRows) :
    (encodeSteinerUnaryCappedRows (steinerUnarySharedCapExpanded request)).length ≤
      (request.1+2)*(encodeSteinerUnarySharedCapRows request).length := by
  have fit := sharedCap_fullFrame_length_le request.1 request.2
  have tail : (sharedCapRawRows request.2).length ≤ (encodeSteinerUnarySharedCapRows request).length := by
    rw [sharedCap_input_length]
    omega
  exact fit.trans (Nat.mul_le_mul_left _ tail)

private theorem sharedCap_init (word : List SharedCapSymbol) :
    initList steinerUnarySharedCapRowsMachine word = sharedCapCfg (some .bound) [] [] word [] := by
  apply congrArg (fun stk : Fin 7 → List SharedCapSymbol =>
    (⟨some .bound,sharedCapInitial,stk⟩ : steinerUnarySharedCapRowsMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem sharedCap_evalInit (word : List SharedCapSymbol) :
    sharedCapTag.configuration (initList steinerUnaryCappedRowsMachine word) =
      sharedCapCfg (some (.evaluate steinerUnaryCappedRowsMachine.main)) [] [] word [] := by
  apply congrArg (fun stk : Fin 7 → List SharedCapSymbol =>
    (⟨some (.evaluate steinerUnaryCappedRowsMachine.main),sharedCapInitial,stk⟩ : steinerUnarySharedCapRowsMachine.Cfg))
  funext i
  change ((initList steinerUnaryCappedRowsMachine word).stk i).map id = _
  rw [List.map_id]
  fin_cases i <;> rfl

private theorem sharedCap_evalHalt (word : List SharedCapSymbol) :
    sharedCapTag.configuration (haltList steinerUnaryCappedRowsMachine word) =
      haltList steinerUnarySharedCapRowsMachine word := by
  apply congrArg (fun stk : Fin 7 → List SharedCapSymbol => (⟨none,sharedCapInitial,stk⟩ : steinerUnarySharedCapRowsMachine.Cfg))
  funext i
  change ((haltList steinerUnaryCappedRowsMachine word).stk i).map id = _
  rw [List.map_id]
  rfl

private def sharedCap_prepare (request : SteinerUnarySharedCapRows) :
    let frame := encodeSteinerUnaryCappedRows (steinerUnarySharedCapExpanded request)
    let Y := frame.length
    EvalsToInTime steinerUnarySharedCapRowsMachine.step
      (initList steinerUnarySharedCapRowsMachine (encodeSteinerUnarySharedCapRows request))
      (some (sharedCapCfg (some (.evaluate steinerUnaryCappedRowsMachine.main)) [] [] frame []))
      (2*request.1+3*Y+4) := by
  rcases request with ⟨n,rows⟩
  let frame := encodeSteinerUnaryCappedRows (steinerUnarySharedCapExpanded (n,rows))
  let Y := frame.length
  have loaded := sharedCap_bound n [] (sharedCapRawRows rows)
  rw [List.append_nil] at loaded
  have copied := sharedCap_processRows n rows [] []
  simp only [List.append_nil] at copied
  have framed := EvalsToInTime.trans _ _ _ _ _ _ loaded copied
  have ended := EvalsToInTime.trans _ _ _ _ _ _ framed
    (sharedCap_one (sharedCap_inputEnd (sharedCapTallies n) frame.reverse))
  have cleared := EvalsToInTime.trans _ _ _ _ _ _ ended (sharedCap_clear n frame.reverse)
  have reordered := sharedCap_restoreFrame [] frame.reverse
  rw [List.reverse_reverse,List.length_reverse,List.append_nil] at reordered
  have prepared := EvalsToInTime.trans _ _ _ _ _ _ cleared reordered
  rw [sharedCap_init]
  refine ⟨prepared.toEvalsTo,?_⟩
  have spent := prepared.steps_le_m
  change prepared.steps ≤ (Y+1)+(n+1+(1+(2*Y+(n+1)))) at spent
  change prepared.steps ≤ 2*n+3*Y+4
  omega

/-- The composed run has a quadratic transition bound in the single-cap unary frame. -/
def steinerUnarySharedCapRowsMachine_run (request : SteinerUnarySharedCapRows) :
    let X := (encodeSteinerUnarySharedCapRows request).length
    TM2OutputsInTime steinerUnarySharedCapRowsMachine (encodeSteinerUnarySharedCapRows request)
      (some (steinerUnarySharedCapRowsAnswer request)) (12*X^2+26*X+6) := by
  let X := (encodeSteinerUnarySharedCapRows request).length
  let frame := encodeSteinerUnaryCappedRows (steinerUnarySharedCapExpanded request)
  let Y := frame.length
  let out := steinerUnarySharedCapRowsAnswer request
  have run := steinerUnaryCappedRowsMachine_run (steinerUnarySharedCapExpanded request)
  have evaluated := sharedCapTag.evaluation (base := steinerUnaryCappedRowsMachine.m)
    (host := sharedCapProgram) (fun _ => rfl) run
  change EvalsToInTime steinerUnarySharedCapRowsMachine.step
    (sharedCapTag.configuration (initList steinerUnaryCappedRowsMachine frame))
    (some (sharedCapTag.configuration (haltList steinerUnaryCappedRowsMachine out))) (9*Y+2) at evaluated
  rw [sharedCap_evalInit,sharedCap_evalHalt] at evaluated
  have all := EvalsToInTime.trans _ _ _ _ _ _ (sharedCap_prepare request) evaluated
  exact ⟨all.toEvalsTo,all.steps_le_m.trans (by
    have nSize : request.1 ≤ X := by
      have length := sharedCap_input_length request
      change X = _ at length
      omega
    have allocated : Y ≤ (request.1+2)*X := encodeSteinerUnarySharedCapExpanded_length_le request
    have scale := Nat.mul_le_mul_right X (Nat.add_le_add_right nSize 2)
    have total : Y ≤ (X+2)*X := allocated.trans scale
    change (9*Y+2)+(2*request.1+3*Y+4) ≤ 12*X^2+26*X+6
    rw [show (X+2)*X = X^2+2*X from by ring] at total
    omega)⟩

/-- The actual shared-cap machine has a quadratic input polynomial. -/
noncomputable def steinerUnarySharedCapRowsMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnarySharedCapRows id steinerUnarySharedCapRowsAnswer where
  tm := steinerUnarySharedCapRowsMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 12*Polynomial.X^2+Polynomial.C 26*Polynomial.X+Polynomial.C 6
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,
      Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_pow] using steinerUnarySharedCapRowsMachine_run request

/-- One cap and the distance/previous-weight pairs in root-major order. -/
def steinerForestSharedCapRequest {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) : SteinerUnarySharedCapRows :=
  (n,List.ofFn fun (root : Fin n) => List.ofFn fun child => (dist (child,root),(inwardHeightWeightRounds dist h)[child.val]))

theorem steinerForestSharedCapRequest_expanded {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) :
    steinerUnarySharedCapExpanded (steinerForestSharedCapRequest dist h) = steinerForestTransferSumRows dist h := by
  unfold steinerUnarySharedCapExpanded steinerForestSharedCapRequest steinerForestTransferSumRows
  rw [List.map_ofFn]
  apply congrArg (@List.ofFn (List SteinerUnaryCappedSumRequest) n)
  funext root
  simp only [Function.comp_apply,List.map_ofFn,steinerForestTransferSumRequest]
  rfl

/-- The exact next vector computed from a shared cap and all supplied pairs. -/
def steinerUnarySharedCapRowsMachine_forestRound {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) :
    let request := steinerForestSharedCapRequest dist h
    let X := (encodeSteinerUnarySharedCapRows request).length
    TM2OutputsInTime steinerUnarySharedCapRowsMachine (encodeSteinerUnarySharedCapRows request)
      (some (encodeSteinerUnaryCappedRowTallies (inwardHeightWeightRounds dist (h+1)).toList)) (12*X^2+26*X+6) := by
  simpa only [steinerUnarySharedCapRowsAnswer,steinerForestSharedCapRequest_expanded,
    steinerUnaryCappedRowsAnswer_forestRound] using steinerUnarySharedCapRowsMachine_run (steinerForestSharedCapRequest dist h)

end OnlineReachabilityPreservers
