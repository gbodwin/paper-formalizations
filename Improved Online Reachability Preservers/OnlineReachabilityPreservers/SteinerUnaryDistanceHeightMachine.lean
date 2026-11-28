import OnlineReachabilityPreservers.SteinerUnaryDistanceRoundMachine
import OnlineReachabilityPreservers.SteinerUnaryRoundPriorArchiveMachine

/-! Reuse one stored distance table across every round of an orientation. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev HeightSymbol := SteinerUnaryCappedRowsSymbol
private abbrev HeightRoundLabel := steinerUnaryDistanceRoundMachine.Λ
private abbrev HeightArchiveLabel := steinerUnaryRoundPriorArchiveMachine.Λ
private instance : Fintype HeightRoundLabel := steinerUnaryDistanceRoundMachine.ΛFin
private instance : Fintype HeightArchiveLabel := steinerUnaryRoundPriorArchiveMachine.ΛFin

private inductive HeightPart where
  | cap | matrix
  deriving DecidableEq

private instance : Fintype HeightPart where
  elems := {.cap,.matrix}
  complete part := by cases part <;> decide

private inductive HeightLabel where
  | height | cap | distances | next
  | copy (part : HeightPart) | restore (part : HeightPart) | loadPrior
  | round (label : HeightRoundLabel) | archive (label : HeightArchiveLabel)
  | finishPrior | clear (part : HeightPart)
  deriving Fintype

private abbrev HeightRegister := Option HeightSymbol ×
  steinerUnaryDistanceRoundMachine.σ × steinerUnaryRoundPriorArchiveMachine.σ
private abbrev HeightProgram := StackMachineTag.Program (Fin 11) HeightSymbol HeightLabel HeightRegister

private def heightRegister (symbol : Option HeightSymbol) : HeightRegister :=
  (symbol,steinerUnaryDistanceRoundMachine.initialState,steinerUnaryRoundPriorArchiveMachine.initialState)

private def heightTally : HeightSymbol := .inr (some true)
private def heightBound : HeightSymbol := .inl false
private def heightField : HeightSymbol := .inr none

private def heightPartSlot : HeightPart → Fin 11
  | .cap => 8
  | .matrix => 9

private def heightRoundTag :
    StackMachineTag HeightSymbol HeightSymbol HeightRoundLabel HeightLabel
      steinerUnaryDistanceRoundMachine.σ HeightRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (none,r,steinerUnaryRoundPriorArchiveMachine.initialState)
  readRegister r := r.2.1
  writeLabel := .round
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def heightArchiveTag :
    StackMachineTag HeightSymbol HeightSymbol HeightArchiveLabel HeightLabel
      steinerUnaryRoundPriorArchiveMachine.σ HeightRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (none,steinerUnaryDistanceRoundMachine.initialState,r)
  readRegister r := r.2.2
  writeLabel := .archive
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def heightRoundSlots : Fin 7 ↪ Fin 11 where
  toFun j := ⟨j.val,j.isLt.trans (by decide)⟩
  inj' := fun _ _ h => Fin.ext (congrArg (Fin.val : Fin 11 → ℕ) h)

private def heightArchiveSlots : Fin 2 ↪ Fin 11 where
  toFun := ![5,10]
  inj' := by intro a b same; fin_cases a <;> fin_cases b <;> simp_all

private def heightArchiveStart : HeightLabel := .archive steinerUnaryRoundPriorArchiveMachine.main
private def heightRoundStart : HeightLabel := .round steinerUnaryDistanceRoundMachine.main

private def heightRoundCode : HeightLabel → StackMachineTag.Program (Fin 7) HeightSymbol HeightLabel HeightRegister
  | .round label => heightRoundTag.returningStatement heightArchiveStart (steinerUnaryDistanceRoundMachine.m label)
  | _ => halt

private def heightArchiveCode : HeightLabel → StackMachineTag.Program (Fin 2) HeightSymbol HeightLabel HeightRegister
  | .archive label => heightArchiveTag.returningStatement .next (steinerUnaryRoundPriorArchiveMachine.m label)
  | _ => halt

private def heightContinue (label : HeightLabel) : HeightProgram :=
  load (fun _ => heightRegister none) (goto fun _ => label)

private def heightStop : HeightProgram := load (fun _ => heightRegister none) halt

private def heightRead (slot : Fin 11) (code : HeightProgram) : HeightProgram :=
  pop slot (fun _ symbol => heightRegister symbol) code

private def heightSeen (r : HeightRegister) : HeightSymbol := r.1.getD heightBound

/- The round occupies slots 0 through 6. Between calls slot 0 is a
copy buffer. Slots 7 through 10 hold the remaining height and the
reversed cap, matrix, and previous-weight vector. -/
private def heightProgram : HeightLabel → HeightProgram
  | .height => heightRead 5 <| branch (fun r => r.1 == some heightTally)
      (push 7 (fun _ => heightTally) (heightContinue .height))
      (heightContinue .cap)
  | .cap => heightRead 5 <| branch (fun r => r.1 == some heightTally)
      (push 8 (fun _ => heightTally) <| push 10 (fun _ => heightField) (heightContinue .cap))
      (push 8 (fun _ => heightBound) (heightContinue .distances))
  | .distances => heightRead 5 <| branch (fun r => r.1.isSome)
      (push 9 heightSeen (heightContinue .distances))
      (heightContinue .next)
  | .next => heightRead 7 <| branch (fun r => r.1.isSome)
      (heightContinue (.copy .matrix))
      (heightContinue .finishPrior)
  | .copy part => heightRead (heightPartSlot part) <| branch (fun r => r.1.isSome)
      (push 0 heightSeen <| push 5 heightSeen (heightContinue (.copy part)))
      (heightContinue (.restore part))
  | .restore part => heightRead 0 <| branch (fun r => r.1.isSome)
      (push (heightPartSlot part) heightSeen (heightContinue (.restore part)))
      (match part with
       | .cap => heightContinue heightRoundStart
       | .matrix => push 5 (fun _ => heightBound) (heightContinue .loadPrior))
  | .loadPrior => heightRead 10 <| branch (fun r => r.1.isSome)
      (push 5 heightSeen (heightContinue .loadPrior))
      (heightContinue (.copy .cap))
  | .round label => StackIndexEmbedding.statement heightRoundSlots (heightRoundCode (.round label))
  | .archive label => StackIndexEmbedding.statement heightArchiveSlots (heightArchiveCode (.archive label))
  | .finishPrior => heightRead 10 <| branch (fun r => r.1.isSome)
      (push 5 (fun r => steinerUnaryRoundPriorToRow (heightSeen r)) (heightContinue .finishPrior))
      (heightContinue (.clear .cap))
  | .clear part => heightRead (heightPartSlot part) <| branch (fun r => r.1.isSome)
      (heightContinue (.clear part))
      (match part with
       | .cap => heightContinue (.clear .matrix)
       | .matrix => heightStop)

/-- One distance matrix and one cap support all unary height rounds.
The previous vector starts at zero and is replaced after each round. -/
abbrev steinerUnaryDistanceHeightMachine : FinTM2 where
  K := Fin 11
  k₀ := 5
  k₁ := 5
  Γ _ := HeightSymbol
  Λ := HeightLabel
  main := .height
  σ := HeightRegister
  initialState := heightRegister none
  m := heightProgram

private def heightTapes (work frame height cap matrix prior : List HeightSymbol) : Fin 11 → List HeightSymbol :=
  ![work,[],[],[],[],frame,[],height,cap,matrix,prior]

private def heightCfg (label : Option HeightLabel) (work frame height cap matrix prior : List HeightSymbol) :
    steinerUnaryDistanceHeightMachine.Cfg :=
  ⟨label,heightRegister none,heightTapes work frame height cap matrix prior⟩

private theorem heightUpdate0 (work frame height cap matrix prior word : List HeightSymbol) :
    Function.update (heightTapes work frame height cap matrix prior) 0 word =
      heightTapes word frame height cap matrix prior := by
  funext i
  fin_cases i <;> simp [heightTapes,Function.update]

private theorem heightUpdate5 (work frame height cap matrix prior word : List HeightSymbol) :
    Function.update (heightTapes work frame height cap matrix prior) 5 word =
      heightTapes work word height cap matrix prior := by
  funext i
  fin_cases i <;> simp [heightTapes,Function.update]

private theorem heightUpdate7 (work frame height cap matrix prior word : List HeightSymbol) :
    Function.update (heightTapes work frame height cap matrix prior) 7 word =
      heightTapes work frame word cap matrix prior := by
  funext i
  fin_cases i <;> simp [heightTapes,Function.update]

private theorem heightUpdate8 (work frame height cap matrix prior word : List HeightSymbol) :
    Function.update (heightTapes work frame height cap matrix prior) 8 word =
      heightTapes work frame height word matrix prior := by
  funext i
  fin_cases i <;> simp [heightTapes,Function.update]

private theorem heightUpdate9 (work frame height cap matrix prior word : List HeightSymbol) :
    Function.update (heightTapes work frame height cap matrix prior) 9 word =
      heightTapes work frame height cap word prior := by
  funext i
  fin_cases i <;> simp [heightTapes,Function.update]

private theorem heightUpdate10 (work frame height cap matrix prior word : List HeightSymbol) :
    Function.update (heightTapes work frame height cap matrix prior) 10 word =
      heightTapes work frame height cap matrix word := by
  funext i
  fin_cases i <;> simp [heightTapes,Function.update]

private abbrev HeightRun (before after : steinerUnaryDistanceHeightMachine.Cfg) (bound : ℕ) :=
  EvalsToInTime steinerUnaryDistanceHeightMachine.step before (some after) bound

private def heightOne {before after : steinerUnaryDistanceHeightMachine.Cfg}
    (step : steinerUnaryDistanceHeightMachine.step before = some after) : HeightRun before after 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := step

private def heightThen {a b c : steinerUnaryDistanceHeightMachine.Cfg} {x y : ℕ}
    (left : HeightRun a b x) (right : HeightRun b c y) : HeightRun a c (x+y) := by
  simpa only [Nat.add_comm] using EvalsToInTime.trans _ _ _ _ _ _ left right

private def heightRelax {a b : steinerUnaryDistanceHeightMachine.Cfg} {x y : ℕ}
    (run : HeightRun a b x) (le : x ≤ y) : HeightRun a b y :=
  ⟨run.toEvalsTo,run.steps_le_m.trans le⟩

private theorem heightReadHeight_push (word remaining : List HeightSymbol) :
    steinerUnaryDistanceHeightMachine.step (heightCfg (some .height) [] (heightTally::word) remaining [] [] []) =
      some (heightCfg (some .height) [] word (heightTally::remaining) [] [] []) := by
  simp only [FinTM2.step,steinerUnaryDistanceHeightMachine,heightCfg,Turing.TM2.step,Turing.TM2.stepAux,
    heightProgram,heightRead,heightUpdate5,heightUpdate7,heightContinue]
  rfl

private theorem heightReadHeight_end (word remaining : List HeightSymbol) :
    steinerUnaryDistanceHeightMachine.step (heightCfg (some .height) [] (heightBound::word) remaining [] [] []) =
      some (heightCfg (some .cap) [] word remaining [] [] []) := by
  simp only [FinTM2.step,steinerUnaryDistanceHeightMachine,heightCfg,Turing.TM2.step,Turing.TM2.stepAux,
    heightProgram,heightRead,heightUpdate5,heightContinue]
  rfl

private theorem heightReplicate_push (n : ℕ) (symbol : HeightSymbol) (word : List HeightSymbol) :
    List.replicate n symbol++symbol::word = List.replicate (n+1) symbol++word := by
  rw [List.replicate_succ',List.append_assoc,List.singleton_append]

private def heightReadHeight (h : ℕ) (word remaining : List HeightSymbol) :
    HeightRun (heightCfg (some .height) [] (List.replicate h heightTally++heightBound::word) remaining [] [] [])
      (heightCfg (some .cap) [] word (List.replicate h heightTally++remaining) [] [] []) (h+1) := by
  induction h generalizing remaining with
  | zero => exact heightOne (heightReadHeight_end word remaining)
  | succ h ih =>
    have run := heightThen (heightOne (heightReadHeight_push _ remaining)) (ih (heightTally::remaining))
    rw [heightReplicate_push] at run
    exact heightRelax run (by omega)

private theorem heightReadCap_push (word height cap prior : List HeightSymbol) :
    steinerUnaryDistanceHeightMachine.step (heightCfg (some .cap) [] (heightTally::word) height cap [] prior) =
      some (heightCfg (some .cap) [] word height (heightTally::cap) [] (heightField::prior)) := by
  simp only [FinTM2.step,steinerUnaryDistanceHeightMachine,heightCfg,Turing.TM2.step,Turing.TM2.stepAux,
    heightProgram,heightRead,heightUpdate5,heightUpdate8,heightUpdate10,heightContinue]
  rfl

private theorem heightReadCap_end (word height cap prior : List HeightSymbol) :
    steinerUnaryDistanceHeightMachine.step (heightCfg (some .cap) [] (heightBound::word) height cap [] prior) =
      some (heightCfg (some .distances) [] word height (heightBound::cap) [] prior) := by
  simp only [FinTM2.step,steinerUnaryDistanceHeightMachine,heightCfg,Turing.TM2.step,Turing.TM2.stepAux,
    heightProgram,heightRead,heightUpdate5,heightUpdate8,heightContinue]
  rfl

private def heightReadCap (n : ℕ) (word height cap prior : List HeightSymbol) :
    HeightRun (heightCfg (some .cap) [] (List.replicate n heightTally++heightBound::word) height cap [] prior)
      (heightCfg (some .distances) [] word height (heightBound::(List.replicate n heightTally++cap)) []
        (List.replicate n heightField++prior)) (n+1) := by
  induction n generalizing cap prior with
  | zero => exact heightOne (heightReadCap_end word height cap prior)
  | succ n ih =>
    have run := heightThen (heightOne (heightReadCap_push _ height cap prior)) (ih (heightTally::cap) (heightField::prior))
    rw [heightReplicate_push,heightReplicate_push] at run
    exact heightRelax run (by omega)

private theorem heightReadMatrix_push (symbol : HeightSymbol) (word height cap matrix prior : List HeightSymbol) :
    steinerUnaryDistanceHeightMachine.step (heightCfg (some .distances) [] (symbol::word) height cap matrix prior) =
      some (heightCfg (some .distances) [] word height cap (symbol::matrix) prior) := by
  simp only [FinTM2.step,steinerUnaryDistanceHeightMachine,heightCfg,Turing.TM2.step,Turing.TM2.stepAux,
    heightProgram,heightRead,heightUpdate5,heightUpdate9,heightContinue,heightSeen]
  rfl

private theorem heightReadMatrix_end (height cap matrix prior : List HeightSymbol) :
    steinerUnaryDistanceHeightMachine.step (heightCfg (some .distances) [] [] height cap matrix prior) =
      some (heightCfg (some .next) [] [] height cap matrix prior) := by
  simp only [FinTM2.step,steinerUnaryDistanceHeightMachine,heightCfg,Turing.TM2.step,Turing.TM2.stepAux,
    heightProgram,heightRead,heightUpdate5,heightContinue,heightRegister]
  rfl

private def heightReadMatrix (word height cap matrix prior : List HeightSymbol) :
    HeightRun (heightCfg (some .distances) [] word height cap matrix prior)
      (heightCfg (some .next) [] [] height cap (word.reverse++matrix) prior) (word.length+1) := by
  induction word generalizing matrix with
  | nil => exact heightOne (heightReadMatrix_end height cap matrix prior)
  | cons symbol word ih =>
    have run := heightThen (heightOne (heightReadMatrix_push symbol word height cap matrix prior))
      (ih (symbol::matrix))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,Nat.add_left_comm] using run

private theorem heightNext_more (remaining cap matrix prior : List HeightSymbol) :
    steinerUnaryDistanceHeightMachine.step (heightCfg (some .next) [] [] (heightTally::remaining) cap matrix prior) =
      some (heightCfg (some (.copy .matrix)) [] [] remaining cap matrix prior) := by
  simp only [FinTM2.step,steinerUnaryDistanceHeightMachine,heightCfg,Turing.TM2.step,Turing.TM2.stepAux,
    heightProgram,heightRead,heightUpdate7,heightContinue]
  rfl

private theorem heightNext_done (cap matrix prior : List HeightSymbol) :
    steinerUnaryDistanceHeightMachine.step (heightCfg (some .next) [] [] [] cap matrix prior) =
      some (heightCfg (some .finishPrior) [] [] [] cap matrix prior) := by
  simp only [FinTM2.step,steinerUnaryDistanceHeightMachine,heightCfg,Turing.TM2.step,Turing.TM2.stepAux,
    heightProgram,heightRead,heightUpdate7,heightContinue]
  rfl

private def heightPartCfg (label : Option HeightLabel) (part : HeightPart)
    (work frame height source other prior : List HeightSymbol) : steinerUnaryDistanceHeightMachine.Cfg :=
  match part with
  | .cap => heightCfg label work frame height source other prior
  | .matrix => heightCfg label work frame height other source prior

private theorem heightCopy_push (part : HeightPart) (symbol : HeightSymbol)
    (work frame height source other prior : List HeightSymbol) :
    steinerUnaryDistanceHeightMachine.step (heightPartCfg (some (.copy part)) part work frame height
      (symbol::source) other prior) =
      some (heightPartCfg (some (.copy part)) part (symbol::work) (symbol::frame) height source other prior) := by
  cases part <;> simp only [heightPartCfg,FinTM2.step,steinerUnaryDistanceHeightMachine,heightCfg,Turing.TM2.step,
    Turing.TM2.stepAux,heightProgram,heightRead,heightPartSlot,heightUpdate8,heightUpdate9,heightUpdate0,
    heightUpdate5,heightContinue,heightSeen] <;> rfl

private theorem heightCopy_end (part : HeightPart) (work frame height other prior : List HeightSymbol) :
    steinerUnaryDistanceHeightMachine.step (heightPartCfg (some (.copy part)) part work frame height [] other prior) =
      some (heightPartCfg (some (.restore part)) part work frame height [] other prior) := by
  cases part <;> simp only [heightPartCfg,FinTM2.step,steinerUnaryDistanceHeightMachine,heightCfg,Turing.TM2.step,
    Turing.TM2.stepAux,heightProgram,heightRead,heightPartSlot,heightUpdate8,heightUpdate9,heightContinue] <;> rfl

private def heightCopyPart (part : HeightPart) (source work frame height other prior : List HeightSymbol) :
    HeightRun (heightPartCfg (some (.copy part)) part work frame height source other prior)
      (heightPartCfg (some (.restore part)) part (source.reverse++work) (source.reverse++frame) height [] other prior)
      (source.length+1) := by
  induction source generalizing work frame with
  | nil => exact heightOne (heightCopy_end part work frame height other prior)
  | cons symbol source ih =>
    have run := heightThen (heightOne (heightCopy_push part symbol work frame height source other prior))
      (ih (symbol::work) (symbol::frame))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,Nat.add_left_comm] using run

private def heightRestoreLabel : HeightPart → HeightLabel
  | .cap => heightRoundStart
  | .matrix => .loadPrior

private def heightRestoredFrame (part : HeightPart) (frame : List HeightSymbol) : List HeightSymbol :=
  match part with
  | .cap => frame
  | .matrix => heightBound::frame

private theorem heightRestore_push (part : HeightPart) (symbol : HeightSymbol)
    (work frame height source other prior : List HeightSymbol) :
    steinerUnaryDistanceHeightMachine.step (heightPartCfg (some (.restore part)) part (symbol::work) frame height
      source other prior) =
      some (heightPartCfg (some (.restore part)) part work frame height (symbol::source) other prior) := by
  cases part <;> simp only [heightPartCfg,FinTM2.step,steinerUnaryDistanceHeightMachine,heightCfg,Turing.TM2.step,
    Turing.TM2.stepAux,heightProgram,heightRead,heightPartSlot,heightUpdate8,heightUpdate9,heightUpdate0,
    heightContinue,heightSeen] <;> rfl

private theorem heightRestore_end (part : HeightPart) (frame height source other prior : List HeightSymbol) :
    steinerUnaryDistanceHeightMachine.step (heightPartCfg (some (.restore part)) part [] frame height source other prior) =
      some (heightPartCfg (some (heightRestoreLabel part)) part [] (heightRestoredFrame part frame)
        height source other prior) := by
  cases part <;> simp only [heightPartCfg,FinTM2.step,steinerUnaryDistanceHeightMachine,heightCfg,Turing.TM2.step,
    Turing.TM2.stepAux,heightProgram,heightRead,heightPartSlot,heightUpdate0,heightUpdate5,heightContinue,
    heightRestoreLabel,heightRestoredFrame] <;> rfl

private def heightRestore (part : HeightPart) (work frame height source other prior : List HeightSymbol) :
    HeightRun (heightPartCfg (some (.restore part)) part work frame height source other prior)
      (heightPartCfg (some (heightRestoreLabel part)) part [] (heightRestoredFrame part frame) height
        (work.reverse++source) other prior) (work.length+1) := by
  induction work generalizing source with
  | nil => exact heightOne (heightRestore_end part frame height source other prior)
  | cons symbol work ih =>
    have run := heightThen (heightOne (heightRestore_push part symbol work frame height source other prior))
      (ih (symbol::source))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,Nat.add_left_comm] using run

private def heightFetch (part : HeightPart) (base frame height other prior : List HeightSymbol) :
    HeightRun (heightPartCfg (some (.copy part)) part [] frame height base.reverse other prior)
      (heightPartCfg (some (heightRestoreLabel part)) part [] (heightRestoredFrame part (base++frame)) height
        base.reverse other prior) (2*base.length+2) := by
  have copy := heightCopyPart part base.reverse [] frame height other prior
  rw [List.reverse_reverse,List.append_nil,List.length_reverse] at copy
  have restore := heightRestore part base (base++frame) height [] other prior
  rw [List.append_nil] at restore
  exact heightRelax (heightThen copy restore) (by omega)

private def heightPriorLabel (finish : Bool) : HeightLabel :=
  if finish then .finishPrior else .loadPrior

private def heightPriorReturn (finish : Bool) : HeightLabel :=
  if finish then .clear .cap else .copy .cap

private def heightPriorSymbol (finish : Bool) (symbol : HeightSymbol) : HeightSymbol :=
  if finish then steinerUnaryRoundPriorToRow symbol else symbol

private theorem heightPrior_push (finish : Bool) (symbol : HeightSymbol)
    (frame height cap matrix prior : List HeightSymbol) :
    steinerUnaryDistanceHeightMachine.step (heightCfg (some (heightPriorLabel finish)) [] frame height cap matrix
      (symbol::prior)) =
      some (heightCfg (some (heightPriorLabel finish)) [] (heightPriorSymbol finish symbol::frame)
        height cap matrix prior) := by
  cases finish <;> simp only [heightPriorLabel,FinTM2.step,steinerUnaryDistanceHeightMachine,heightCfg,Turing.TM2.step,
    Turing.TM2.stepAux,heightProgram,heightRead,heightUpdate10,heightUpdate5,heightContinue,heightSeen,heightPriorSymbol,
    Bool.false_eq_true,ite_false,ite_true] <;> rfl

private theorem heightPrior_end (finish : Bool) (frame height cap matrix : List HeightSymbol) :
    steinerUnaryDistanceHeightMachine.step (heightCfg (some (heightPriorLabel finish)) [] frame height cap matrix []) =
      some (heightCfg (some (heightPriorReturn finish)) [] frame height cap matrix []) := by
  cases finish <;> simp only [heightPriorLabel,FinTM2.step,steinerUnaryDistanceHeightMachine,heightCfg,Turing.TM2.step,
    Turing.TM2.stepAux,heightProgram,heightRead,heightUpdate10,heightContinue,heightPriorReturn,
    Bool.false_eq_true,ite_false,ite_true] <;> rfl

private def heightPrior (finish : Bool) (prior frame height cap matrix : List HeightSymbol) :
    HeightRun (heightCfg (some (heightPriorLabel finish)) [] frame height cap matrix prior)
      (heightCfg (some (heightPriorReturn finish)) [] ((prior.map (heightPriorSymbol finish)).reverse++frame)
        height cap matrix []) (prior.length+1) := by
  induction prior generalizing frame with
  | nil => exact heightOne (heightPrior_end finish frame height cap matrix)
  | cons symbol prior ih =>
    have run := heightThen (heightOne (heightPrior_push finish symbol frame height cap matrix prior))
      (ih (heightPriorSymbol finish symbol::frame))
    simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,
      Nat.add_left_comm] using run

private def heightClearReturn : HeightPart → Option HeightLabel
  | .cap => some (.clear .matrix)
  | .matrix => none

private theorem heightClear_pop (part : HeightPart) (symbol : HeightSymbol) (frame source other : List HeightSymbol) :
    steinerUnaryDistanceHeightMachine.step (heightPartCfg (some (.clear part)) part [] frame [] (symbol::source) other []) =
      some (heightPartCfg (some (.clear part)) part [] frame [] source other []) := by
  cases part <;> simp only [heightPartCfg,FinTM2.step,steinerUnaryDistanceHeightMachine,heightCfg,Turing.TM2.step,
    Turing.TM2.stepAux,heightProgram,heightRead,heightPartSlot,heightUpdate8,heightUpdate9,heightContinue] <;> rfl

private theorem heightClear_end (part : HeightPart) (frame other : List HeightSymbol) :
    steinerUnaryDistanceHeightMachine.step (heightPartCfg (some (.clear part)) part [] frame [] [] other []) =
      some (heightPartCfg (heightClearReturn part) part [] frame [] [] other []) := by
  cases part <;> simp only [heightPartCfg,FinTM2.step,steinerUnaryDistanceHeightMachine,heightCfg,Turing.TM2.step,
    Turing.TM2.stepAux,heightProgram,heightRead,heightPartSlot,heightUpdate8,heightUpdate9,heightContinue,heightStop,
    heightClearReturn] <;> rfl

private def heightClear (part : HeightPart) (source frame other : List HeightSymbol) :
    HeightRun (heightPartCfg (some (.clear part)) part [] frame [] source other [])
      (heightPartCfg (heightClearReturn part) part [] frame [] [] other []) (source.length+1) := by
  induction source with
  | nil => exact heightOne (heightClear_end part frame other)
  | cons symbol source ih =>
    have run := heightThen (heightOne (heightClear_pop part symbol frame source other)) ih
    simpa only [List.length_cons,Nat.add_left_comm] using run

private theorem heightHostedTapes {k : ℕ} (slots : Fin k ↪ Fin 11)
    (active : Fin k → List HeightSymbol) (extra expected : Fin 11 → List HeightSymbol)
    (live : ∀ i, active i = expected (slots i)) (passive : ∀ i, (∀ j, slots j ≠ i) → extra i = expected i) :
    StackIndexEmbedding.tapesAt slots active extra = expected := by
  classical
  funext i
  by_cases found : ∃ j, slots j = i
  · obtain ⟨j,rfl⟩ := found
    rw [StackIndexEmbedding.tapesAt_image]
    exact live j
  · have outside (j) : slots j ≠ i := fun equal => found ⟨j,equal⟩
    rw [StackIndexEmbedding.tapesAt_extra slots _ _ outside]
    exact passive i outside

private noncomputable def heightRoundHosted (height cap matrix : List HeightSymbol)
    (c : steinerUnaryDistanceRoundMachine.Cfg) : steinerUnaryDistanceHeightMachine.Cfg :=
  StackIndexEmbedding.configuration heightRoundSlots (heightTapes [] [] height cap matrix [])
    (heightRoundTag.returningConfiguration heightArchiveStart c)

private theorem heightRoundHosted_step (height cap matrix : List HeightSymbol)
    {c after : steinerUnaryDistanceRoundMachine.Cfg} (move : steinerUnaryDistanceRoundMachine.step c = some after) :
    steinerUnaryDistanceHeightMachine.step (heightRoundHosted height cap matrix c) =
      some (heightRoundHosted height cap matrix after) := by
  have tagged := heightRoundTag.step_embedded_return heightArchiveStart
    (base := steinerUnaryDistanceRoundMachine.m) (host := heightRoundCode) (fun _ => rfl) move
  have hosted := StackIndexEmbedding.step_on heightRoundSlots (base := heightRoundCode)
    (heightTapes [] [] height cap matrix []) (heightRoundTag.returningConfiguration heightArchiveStart c)
  rw [tagged] at hosted
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact hosted

private theorem heightRoundHosted_tapes (height cap matrix word : List HeightSymbol)
    (c : steinerUnaryDistanceRoundMachine.Cfg) (tapes : c.stk = ![[],[],[],[],[],word,[]]) :
    (heightRoundHosted height cap matrix c).stk = heightTapes [] word height cap matrix [] := by
  change StackIndexEmbedding.tapesAt heightRoundSlots (fun i => (c.stk i).map id)
    (heightTapes [] [] height cap matrix []) = _
  apply heightHostedTapes
  · intro i
    rw [List.map_id,tapes]
    fin_cases i <;> rfl
  · intro i outside
    have other : i ≠ 5 := fun equal => outside 5 equal.symm
    have same := congrFun (heightUpdate5 [] [] height cap matrix [] word) i
    rw [Function.update_of_ne other] at same
    exact same

private theorem heightRoundHosted_init (height cap matrix word : List HeightSymbol) :
    heightRoundHosted height cap matrix (initList steinerUnaryDistanceRoundMachine word) =
      heightCfg (some heightRoundStart) [] word height cap matrix [] := by
  apply congrArg (fun tapes : Fin 11 → List HeightSymbol =>
    (⟨some heightRoundStart,heightRegister none,tapes⟩ : steinerUnaryDistanceHeightMachine.Cfg))
  apply heightRoundHosted_tapes
  funext i
  fin_cases i <;> rfl

private theorem heightRoundHosted_halt (height cap matrix word : List HeightSymbol) :
    heightRoundHosted height cap matrix (haltList steinerUnaryDistanceRoundMachine word) =
      heightCfg (some heightArchiveStart) [] word height cap matrix [] := by
  apply congrArg (fun tapes : Fin 11 → List HeightSymbol =>
    (⟨some heightArchiveStart,heightRegister none,tapes⟩ : steinerUnaryDistanceHeightMachine.Cfg))
  apply heightRoundHosted_tapes
  funext i
  fin_cases i <;> rfl

private def heightRoundCost (X : ℕ) : ℕ :=
  let C := X^2+X
  12*C^2+26*C+4*X^2+7*X+11

private theorem heightRoundCost_mono : Monotone heightRoundCost := by
  intro x y le
  have sq : x^2 ≤ y^2 := Nat.pow_le_pow_left le 2
  have both : x^2+x ≤ y^2+y := by omega
  have fourth := Nat.pow_le_pow_left both 2
  change 12*(x^2+x)^2+26*(x^2+x)+4*x^2+7*x+11 ≤ 12*(y^2+y)^2+26*(y^2+y)+4*y^2+7*y+11
  omega

private noncomputable def heightRoundRun {n : ℕ} (dist : Fin n × Fin n → ℕ) (past : ℕ)
    (height cap matrix : List HeightSymbol) :
    let input := encodeSteinerUnaryDistanceRound (steinerForestDistanceRoundRequest dist past)
    let output := encodeSteinerUnaryCappedRowTallies (inwardHeightWeightRounds dist (past+1)).toList
    HeightRun (heightCfg (some heightRoundStart) [] input height cap matrix [])
      (heightCfg (some heightArchiveStart) [] output height cap matrix []) (heightRoundCost input.length) := by
  let run := steinerUnaryDistanceRoundMachine_forestRound dist past
  have hosted := iterate_map_some (heightRoundHosted height cap matrix)
    (fun move => heightRoundHosted_step height cap matrix move) run.steps run.evals_in_steps
  rw [heightRoundHosted_init,heightRoundHosted_halt] at hosted
  exact ⟨⟨run.steps,hosted⟩,run.steps_le_m⟩

private noncomputable def heightArchiveHosted (height cap matrix : List HeightSymbol)
    (c : steinerUnaryRoundPriorArchiveMachine.Cfg) : steinerUnaryDistanceHeightMachine.Cfg :=
  StackIndexEmbedding.configuration heightArchiveSlots (heightTapes [] [] height cap matrix [])
    (heightArchiveTag.returningConfiguration .next c)

private theorem heightArchiveHosted_step (height cap matrix : List HeightSymbol)
    {c after : steinerUnaryRoundPriorArchiveMachine.Cfg}
    (move : steinerUnaryRoundPriorArchiveMachine.step c = some after) :
    steinerUnaryDistanceHeightMachine.step (heightArchiveHosted height cap matrix c) =
      some (heightArchiveHosted height cap matrix after) := by
  have tagged := heightArchiveTag.step_embedded_return HeightLabel.next
    (base := steinerUnaryRoundPriorArchiveMachine.m) (host := heightArchiveCode) (fun _ => rfl) move
  have hosted := StackIndexEmbedding.step_on heightArchiveSlots (base := heightArchiveCode)
    (heightTapes [] [] height cap matrix []) (heightArchiveTag.returningConfiguration .next c)
  rw [tagged] at hosted
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact hosted

private theorem heightArchiveHosted_tapes (height cap matrix word prior : List HeightSymbol)
    (c : steinerUnaryRoundPriorArchiveMachine.Cfg) (tapes : c.stk = ![word,prior]) :
    (heightArchiveHosted height cap matrix c).stk = heightTapes [] word height cap matrix prior := by
  change StackIndexEmbedding.tapesAt heightArchiveSlots (fun i => (c.stk i).map id)
    (heightTapes [] [] height cap matrix []) = _
  apply heightHostedTapes
  · intro i
    rw [List.map_id,tapes]
    fin_cases i <;> rfl
  · intro i outside
    have other5 : i ≠ 5 := fun equal => outside 0 equal.symm
    have other10 : i ≠ 10 := fun equal => outside 1 equal.symm
    have same5 := congrFun (heightUpdate5 [] [] height cap matrix [] word) i
    have same10 := congrFun (heightUpdate10 [] word height cap matrix [] prior) i
    rw [Function.update_of_ne other5] at same5
    rw [Function.update_of_ne other10] at same10
    exact same5.trans same10

private theorem heightArchiveHosted_init (height cap matrix word : List HeightSymbol) :
    heightArchiveHosted height cap matrix (initList steinerUnaryRoundPriorArchiveMachine word) =
      heightCfg (some heightArchiveStart) [] word height cap matrix [] := by
  apply congrArg (fun tapes : Fin 11 → List HeightSymbol =>
    (⟨some heightArchiveStart,heightRegister none,tapes⟩ : steinerUnaryDistanceHeightMachine.Cfg))
  apply heightArchiveHosted_tapes
  funext i
  fin_cases i <;> rfl

private theorem heightArchiveHosted_halt (height cap matrix prior : List HeightSymbol) :
    heightArchiveHosted height cap matrix (haltList steinerUnaryRoundPriorArchiveMachine prior) =
      heightCfg (some .next) [] [] height cap matrix prior := by
  apply congrArg (fun tapes : Fin 11 → List HeightSymbol =>
    (⟨some .next,heightRegister none,tapes⟩ : steinerUnaryDistanceHeightMachine.Cfg))
  apply heightArchiveHosted_tapes
  funext i
  fin_cases i <;> rfl

private noncomputable def heightArchiveRun (height cap matrix : List HeightSymbol) (values : List ℕ) :
    let input := encodeSteinerUnaryCappedRowTallies values
    let prior := encodeSteinerUnaryRoundPriorVector values
    HeightRun (heightCfg (some heightArchiveStart) [] input height cap matrix [])
      (heightCfg (some .next) [] [] height cap matrix prior.reverse) (prior.length+1) := by
  let run := steinerUnaryRoundPriorArchiveMachine_run values
  have hosted := iterate_map_some (heightArchiveHosted height cap matrix)
    (fun move => heightArchiveHosted_step height cap matrix move) run.steps run.evals_in_steps
  rw [heightArchiveHosted_init,heightArchiveHosted_halt] at hosted
  have same := congrArg List.length (encodeSteinerUnaryRoundPriorVector_map_toRows values)
  rw [List.length_map] at same
  refine ⟨⟨run.steps,hosted⟩,?_⟩
  change run.steps ≤ (encodeSteinerUnaryRoundPriorVector values).length+1
  rw [same]
  exact run.steps_le_m

private def heightDistFrame {n : ℕ} (dist : Fin n × Fin n → ℕ) : List HeightSymbol :=
  encodeSteinerUnaryRoundDistances (List.ofFn fun root => List.ofFn fun child => dist (child,root))

private def heightPriorFrame {n : ℕ} (dist : Fin n × Fin n → ℕ) (depth : ℕ) : List HeightSymbol :=
  encodeSteinerUnaryRoundPriorVector (inwardHeightWeightRounds dist depth).toList

private theorem heightRound_components {n : ℕ} (dist : Fin n × Fin n → ℕ) (past : ℕ) :
    encodeSteinerUnaryDistanceRound (steinerForestDistanceRoundRequest dist past) =
      encodeSteinerUnaryRoundCap n++heightPriorFrame dist past++heightBound::heightDistFrame dist := by
  rw [encodeSteinerUnaryDistanceRound_components]
  simp only [steinerForestDistanceRoundRequest,heightPriorFrame,heightDistFrame,heightBound,
    List.map_ofFn,Function.comp_def,Vector.toList_ofFn]

private theorem heightInput_roundLength {n : ℕ} (dist : Fin n × Fin n → ℕ) (past : ℕ) :
    (encodeSteinerUnaryDistanceRound (steinerForestDistanceRoundRequest dist past)).length =
      (encodeSteinerUnaryRoundCap n).length+(heightPriorFrame dist past).length+1+(heightDistFrame dist).length := by
  rw [heightRound_components]
  simp only [List.length_append,List.length_cons]
  omega

private noncomputable def heightCycle {n : ℕ} (dist : Fin n × Fin n → ℕ) (past : ℕ)
    (remaining : List HeightSymbol) :
    let cap := encodeSteinerUnaryRoundCap n
    let matrix := heightDistFrame dist
    let prior := heightPriorFrame dist past
    let next := heightPriorFrame dist (past+1)
    let X := cap.length+prior.length+1+matrix.length
    HeightRun (heightCfg (some .next) [] [] (heightTally::remaining) cap.reverse matrix.reverse prior.reverse)
      (heightCfg (some .next) [] [] remaining cap.reverse matrix.reverse next.reverse)
      (2*matrix.length+2*cap.length+prior.length+next.length+heightRoundCost X+7) := by
  let cap := encodeSteinerUnaryRoundCap n
  let matrix := heightDistFrame dist
  let prior := heightPriorFrame dist past
  let next := heightPriorFrame dist (past+1)
  have start := heightOne (heightNext_more remaining cap.reverse matrix.reverse prior.reverse)
  have matrixRun := heightFetch .matrix matrix [] remaining cap.reverse prior.reverse
  simp only [heightPartCfg,heightRestoreLabel,heightRestoredFrame,List.append_nil] at matrixRun
  have priorRun := heightPrior false prior.reverse (heightBound::matrix) remaining cap.reverse matrix.reverse
  have identity : heightPriorSymbol false = id := rfl
  simp only [heightPriorLabel,heightPriorReturn,Bool.false_eq_true,ite_false,identity,List.map_id_fun,id_eq,
    List.reverse_reverse,List.length_reverse] at priorRun
  have capRun := heightFetch .cap cap (prior++heightBound::matrix) remaining matrix.reverse []
  simp only [heightPartCfg,heightRestoreLabel,heightRestoredFrame] at capRun
  have round := heightRoundRun dist past remaining cap.reverse matrix.reverse
  dsimp only at round
  rw [heightInput_roundLength,heightRound_components,List.append_assoc] at round
  have nextRun := heightArchiveRun remaining cap.reverse matrix.reverse (inwardHeightWeightRounds dist (past+1)).toList
  have run := heightThen (heightThen (heightThen (heightThen (heightThen start matrixRun) priorRun) capRun) round) nextRun
  exact heightRelax run (by dsimp only [cap,matrix,prior,next,heightPriorFrame]; omega)

private noncomputable def heightFinish (cap matrix : List HeightSymbol) (values : List ℕ) :
    let prior := encodeSteinerUnaryRoundPriorVector values
    let output := encodeSteinerUnaryCappedRowTallies values
    HeightRun (heightCfg (some .next) [] [] [] cap.reverse matrix.reverse prior.reverse)
      (heightCfg none [] output [] [] [] []) (prior.length+cap.length+matrix.length+4) := by
  let prior := encodeSteinerUnaryRoundPriorVector values
  let output := encodeSteinerUnaryCappedRowTallies values
  have start := heightOne (heightNext_done cap.reverse matrix.reverse prior.reverse)
  have restore := heightPrior true prior.reverse [] [] cap.reverse matrix.reverse
  have mapper : heightPriorSymbol true = steinerUnaryRoundPriorToRow := rfl
  simp only [heightPriorLabel,heightPriorReturn,mapper,ite_true,List.map_reverse,List.reverse_reverse,
    List.length_reverse,List.append_nil] at restore
  have same : prior.map steinerUnaryRoundPriorToRow = output := encodeSteinerUnaryRoundPriorVector_map_toRows values
  rw [same] at restore
  have clearCap := heightClear .cap cap.reverse output matrix.reverse
  have clearMatrix := heightClear .matrix matrix.reverse output []
  simp only [heightPartCfg,heightClearReturn,List.length_reverse] at clearCap clearMatrix
  refine heightRelax (heightThen (heightThen (heightThen start restore) clearCap) clearMatrix) ?_
  change _ ≤ prior.length+cap.length+matrix.length+4
  omega

/-- A unary round count, one cap and the distance rows in root order. -/
def encodeSteinerUnaryDistanceHeight {n : ℕ} (dist : Fin n × Fin n → ℕ) (height : ℕ) :
    List SteinerUnaryCappedRowsSymbol :=
  List.replicate height heightTally++heightBound::(encodeSteinerUnaryRoundCap n++heightDistFrame dist)

private theorem heightInput_length {n : ℕ} (dist : Fin n × Fin n → ℕ) (height : ℕ) :
    (encodeSteinerUnaryDistanceHeight dist height).length =
      height+1+(encodeSteinerUnaryRoundCap n).length+(heightDistFrame dist).length := by
  simp only [encodeSteinerUnaryDistanceHeight,List.length_append,List.length_replicate,List.length_cons]
  omega

private theorem heightCap_length (n : ℕ) : (encodeSteinerUnaryRoundCap n).length = n+1 := by
  simp [encodeSteinerUnaryRoundCap]

private theorem heightInit (word : List HeightSymbol) :
    initList steinerUnaryDistanceHeightMachine word = heightCfg (some .height) [] word [] [] [] [] := by
  apply congrArg (fun tapes : Fin 11 → List HeightSymbol =>
    (⟨some .height,heightRegister none,tapes⟩ : steinerUnaryDistanceHeightMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem heightHalt (word : List HeightSymbol) :
    haltList steinerUnaryDistanceHeightMachine word = heightCfg none [] word [] [] [] [] := by
  apply congrArg (fun tapes : Fin 11 → List HeightSymbol =>
    (⟨none,heightRegister none,tapes⟩ : steinerUnaryDistanceHeightMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private def heightSetup {n : ℕ} (dist : Fin n × Fin n → ℕ) (height : ℕ) :
    let input := encodeSteinerUnaryDistanceHeight dist height
    let cap := encodeSteinerUnaryRoundCap n
    let matrix := heightDistFrame dist
    let prior := heightPriorFrame dist 0
    HeightRun (initList steinerUnaryDistanceHeightMachine input)
      (heightCfg (some .next) [] [] (List.replicate height heightTally) cap.reverse matrix.reverse prior.reverse)
      (input.length+1) := by
  let cap := encodeSteinerUnaryRoundCap n
  let matrix := heightDistFrame dist
  let remaining := List.replicate height heightTally
  have loadHeight := heightReadHeight height (cap++matrix) []
  rw [List.append_nil] at loadHeight
  have capFront : cap++matrix = List.replicate n heightTally++heightBound::matrix := by
    simp only [cap,encodeSteinerUnaryRoundCap,heightTally,heightBound,List.append_assoc,List.singleton_append]
  have inputWord : encodeSteinerUnaryDistanceHeight dist height = List.replicate height heightTally++
      heightBound::(List.replicate n heightTally++heightBound::matrix) := by
    change List.replicate height heightTally++heightBound::(cap++matrix) = _
    rw [capFront]
  rw [capFront] at loadHeight
  have loadCap := heightReadCap n matrix remaining [] []
  simp only [List.append_nil] at loadCap
  have capOrder : heightBound::List.replicate n heightTally = cap.reverse := by
    simp [cap,encodeSteinerUnaryRoundCap,heightBound,heightTally]
  have zeros : (heightPriorFrame dist 0).reverse = List.replicate n heightField := by
    simp [heightPriorFrame,inwardHeightWeightRounds,encodeSteinerUnaryRoundPriorVector_zero,heightField]
  rw [capOrder,← zeros] at loadCap
  have loadMatrix := heightReadMatrix matrix remaining cap.reverse [] (heightPriorFrame dist 0).reverse
  rw [List.append_nil] at loadMatrix
  dsimp only
  rw [heightInit,heightInput_length,heightCap_length,inputWord]
  refine heightRelax (heightThen (heightThen loadHeight loadCap) loadMatrix) ?_
  change _ ≤ height+1+(n+1)+matrix.length+1
  omega

private def heightPriorLimit (height X : ℕ) : ℕ := X*(X^(height+1)+1)

private def heightCycleLimit (height X : ℕ) : ℕ :=
  let P := heightPriorLimit height X
  2*X+2*P+heightRoundCost (X+P)+7

private def heightFinishLimit (height X : ℕ) : ℕ := heightPriorLimit height X+X+4

private theorem heightPrior_bounded {n : ℕ} (dist : Fin n × Fin n → ℕ) {depth height X : ℕ}
    (depth_le : depth ≤ height) (cap_le : n+1 ≤ X) :
    (heightPriorFrame dist depth).length ≤ heightPriorLimit height X := by
  have frame := encodeSteinerUnaryRoundPriorVector_length_le (inwardHeightWeightRounds dist depth)
    (fun i => inwardHeightWeightRounds_get_le dist depth i)
  have roundBound : inwardHeightWeightRoundBound n depth ≤ (n+1)^(depth+1) :=
    (Nat.le_add_right _ _).trans (inwardHeightWeightRoundBound_add_le n depth)
  have power : (n+1)^(depth+1) ≤ X^(height+1) :=
    (Nat.pow_le_pow_left cap_le _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  exact frame.trans (Nat.mul_le_mul (by omega) (Nat.add_le_add_right (roundBound.trans power) 1))

private noncomputable def heightRunFrom {n : ℕ} (dist : Fin n × Fin n → ℕ) (height X past remaining : ℕ)
    (depth_le : past+remaining ≤ height)
    (available : (encodeSteinerUnaryRoundCap n).length+1+(heightDistFrame dist).length ≤ X) :
    let cap := encodeSteinerUnaryRoundCap n
    let matrix := heightDistFrame dist
    let prior := heightPriorFrame dist past
    let output := encodeSteinerUnaryCappedRowTallies (inwardHeightWeightRounds dist (past+remaining)).toList
    HeightRun (heightCfg (some .next) [] [] (List.replicate remaining heightTally) cap.reverse matrix.reverse prior.reverse)
      (heightCfg none [] output [] [] [] []) (remaining*heightCycleLimit height X+heightFinishLimit height X) := by
  let cap := encodeSteinerUnaryRoundCap n
  let matrix := heightDistFrame dist
  have cap_le : n+1 ≤ X := by rw [heightCap_length] at available; omega
  induction remaining generalizing past with
  | zero =>
    have len := heightPrior_bounded dist (depth_le := show past ≤ height by omega) cap_le
    have run := heightFinish cap matrix (inwardHeightWeightRounds dist past).toList
    change HeightRun _ _ ((heightPriorFrame dist past).length+cap.length+matrix.length+4) at run
    simp only [Nat.add_zero,Nat.zero_mul,Nat.zero_add]
    refine heightRelax run ?_
    unfold heightFinishLimit
    change cap.length+1+matrix.length ≤ X at available
    omega
  | succ remaining ih =>
    have len := heightPrior_bounded dist (depth_le := show past ≤ height by omega) cap_le
    have nextLen := heightPrior_bounded dist (depth_le := show past+1 ≤ height by omega) cap_le
    have roundLen : cap.length+(heightPriorFrame dist past).length+1+matrix.length ≤
        X+heightPriorLimit height X := by
      change cap.length+1+matrix.length ≤ X at available
      omega
    have roundCost := heightRoundCost_mono roundLen
    have step := heightCycle dist past (List.replicate remaining heightTally)
    have stepCost : 2*matrix.length+2*cap.length+(heightPriorFrame dist past).length+
        (heightPriorFrame dist (past+1)).length+
        heightRoundCost (cap.length+(heightPriorFrame dist past).length+1+matrix.length)+7 ≤
        heightCycleLimit height X := by
      change cap.length+1+matrix.length ≤ X at available
      change _ ≤ 2*X+2*heightPriorLimit height X+heightRoundCost (X+heightPriorLimit height X)+7
      omega
    have shortStep := heightRelax step stepCost
    have tail := ih (past+1) (by omega)
    have same : past+1+remaining = past+(remaining+1) := by omega
    rw [same] at tail
    refine heightRelax (heightThen shortStep tail) ?_
    rw [show (remaining+1)*heightCycleLimit height X =
      remaining*heightCycleLimit height X+heightCycleLimit height X from Nat.succ_mul _ _]
    omega

/-- The transition bound is a polynomial in the encoded input length
for each fixed height. -/
def steinerUnaryDistanceHeightTime (height inputLength : ℕ) : ℕ :=
  inputLength+1+height*heightCycleLimit height inputLength+heightFinishLimit height inputLength

/-- Compute the exact rooted vector after the supplied number of rounds
from one stored distance table in either selected orientation. -/
noncomputable def steinerUnaryDistanceHeightMachine_run {n : ℕ} (dist : Fin n × Fin n → ℕ) (height : ℕ) :
    let input := encodeSteinerUnaryDistanceHeight dist height
    TM2OutputsInTime steinerUnaryDistanceHeightMachine input
      (some (encodeSteinerUnaryCappedRowTallies (inwardHeightWeightRounds dist height).toList))
      (steinerUnaryDistanceHeightTime height input.length) := by
  let input := encodeSteinerUnaryDistanceHeight dist height
  have enough : (encodeSteinerUnaryRoundCap n).length+1+(heightDistFrame dist).length ≤ input.length := by
    dsimp only [input]
    rw [heightInput_length]
    omega
  have setup := heightSetup dist height
  have rounds := heightRunFrom dist height input.length 0 height (by omega) enough
  simp only [Nat.zero_add] at rounds
  change HeightRun (initList steinerUnaryDistanceHeightMachine input) (haltList steinerUnaryDistanceHeightMachine _) _
  rw [heightHalt]
  have run := heightThen setup rounds
  refine heightRelax run ?_
  change _ ≤ input.length+1+height*heightCycleLimit height input.length+heightFinishLimit height input.length
  dsimp only [input]
  omega

/-- The actual repeated-round machine has a polynomial running-time
certificate on the typed distance input for each fixed height. -/
noncomputable def steinerUnaryDistanceHeightMachine_polytime (height : ℕ) :
    TM2ComputableInPolyTime
      (fun request : Σ n : ℕ, (Fin n × Fin n → ℕ) => encodeSteinerUnaryDistanceHeight request.2 height)
      id (fun request => encodeSteinerUnaryCappedRowTallies (inwardHeightWeightRounds request.2 height).toList) where
  tm := steinerUnaryDistanceHeightMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time :=
    let X : Polynomial ℕ := Polynomial.X
    let P := X*(X^(height+1)+Polynomial.C 1)
    let T := X+P
    let C := T^2+T
    X+Polynomial.C 1+Polynomial.C height*
      (Polynomial.C 2*X+Polynomial.C 2*P+
        (Polynomial.C 12*C^2+Polynomial.C 26*C+Polynomial.C 4*T^2+Polynomial.C 7*T+Polynomial.C 11)+Polynomial.C 7)+
      (P+X+Polynomial.C 4)
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_pow,steinerUnaryDistanceHeightTime,heightCycleLimit,heightPriorLimit,
      heightFinishLimit,heightRoundCost] using steinerUnaryDistanceHeightMachine_run request.2 height

end OnlineReachabilityPreservers
