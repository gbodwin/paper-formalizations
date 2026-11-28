import OnlineReachabilityPreservers.SteinerUnaryHopTransferCandidateMachine
import OnlineReachabilityPreservers.SteinerUnaryMinimumMachine

/-! Prepare one minimum request by evaluating its supplied unary transfers. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev HopRowSymbol := SteinerUnaryCappedRowsSymbol
private abbrev HopRowCandidateLabel := steinerUnaryHopTransferCandidateMachine.Λ
private abbrev HopRowCandidateRegister := steinerUnaryHopTransferCandidateMachine.σ
private instance : Fintype HopRowCandidateLabel := steinerUnaryHopTransferCandidateMachine.ΛFin

private inductive HopRowMove where
  | restore | archive | finish
  deriving DecidableEq

private instance : Fintype HopRowMove where
  elems := {.restore,.archive,.finish}
  complete phase := by cases phase <;> decide

private inductive HopRowLabel where
  | prefix | cell
  | move (phase : HopRowMove)
  | candidate (label : HopRowCandidateLabel)
  deriving Fintype

private abbrev HopRowRegister := Option HopRowSymbol × HopRowCandidateRegister
private abbrev HopRowProgram := StackMachineTag.Program (Fin 6) HopRowSymbol HopRowLabel HopRowRegister

private def hopRowRegister (seen : Option HopRowSymbol) : HopRowRegister :=
  (seen,steinerUnaryHopTransferCandidateMachine.initialState)

private def hopRowTally : HopRowSymbol := Sum.inr (some true)
private def hopRowField : HopRowSymbol := Sum.inr none
private def hopRowCell : HopRowSymbol := Sum.inl false

private def hopRowTag :
    StackMachineTag HopRowSymbol HopRowSymbol HopRowCandidateLabel HopRowLabel HopRowCandidateRegister HopRowRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (none,r)
  readRegister := Prod.snd
  writeLabel := .candidate
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def hopRowSlots : Fin 3 ↪ Fin 6 where
  toFun i := ⟨i.val,i.isLt.trans (by decide)⟩
  inj' := fun _ _ eq => Fin.ext (congrArg (Fin.val : Fin 6 → ℕ) eq)

private def hopRowCandidateStart : HopRowLabel := .candidate steinerUnaryHopTransferCandidateMachine.main

private def hopRowCandidateCode : HopRowLabel →
    StackMachineTag.Program (Fin 3) HopRowSymbol HopRowLabel HopRowRegister
  | .candidate label => hopRowTag.returningStatement (.move .archive) (steinerUnaryHopTransferCandidateMachine.m label)
  | _ => halt

private def hopRowRead (slot : Fin 6) (code : HopRowProgram) : HopRowProgram :=
  pop slot (fun _ seen => hopRowRegister seen) code

private def hopRowSeen (r : HopRowRegister) : HopRowSymbol := r.1.getD hopRowCell

private def hopRowNext (label : HopRowLabel) : HopRowProgram :=
  load (fun _ => hopRowRegister none) (goto fun _ => label)

private def hopRowMoveSource : HopRowMove → Fin 6
  | .restore => 4
  | .archive => 2
  | .finish => 5

private def hopRowMoveDestination : HopRowMove → Fin 6
  | .restore => 0
  | .archive => 5
  | .finish => 0

private def hopRowMoveEnd : HopRowMove → HopRowProgram
  | .restore => hopRowNext hopRowCandidateStart
  | .archive => push 5 (fun _ => hopRowField) (hopRowNext .cell)
  | .finish => load (fun _ => hopRowRegister none) halt

/- Slots 0–2 run the saved candidate. Slot 3 holds unread row data,
4 reverses the next cell, and 5 accumulates the reverse minimum frame. -/
private def hopRowProgram : HopRowLabel → HopRowProgram
  | .prefix => hopRowRead 3 <| push 5 hopRowSeen <|
      branch (fun r => r.1 == some hopRowField) (hopRowNext .cell) (hopRowNext .prefix)
  | .cell => hopRowRead 3 <| branch (fun r => r.1.isSome)
      (branch (fun r => r.1 == some hopRowCell)
        (hopRowNext (.move .restore)) (push 4 hopRowSeen (hopRowNext .cell)))
      (hopRowNext (.move .finish))
  | .move phase => hopRowRead (hopRowMoveSource phase) <| branch (fun r => r.1.isSome)
      (push (hopRowMoveDestination phase) hopRowSeen (hopRowNext (.move phase))) (hopRowMoveEnd phase)
  | .candidate label => StackIndexEmbedding.statement hopRowSlots (hopRowCandidateCode (.candidate label))

/-- Convert a row of supplied transfer cells into the exact fields for
the native minimum machine. Each candidate is computed on live tapes. -/
abbrev steinerUnaryHopMinimumRowFrameMachine : FinTM2 where
  K := Fin 6
  k₀ := 3
  k₁ := 0
  Γ _ := HopRowSymbol
  Λ := HopRowLabel
  main := .prefix
  σ := HopRowRegister
  initialState := hopRowRegister none
  m := hopRowProgram

private def hopRowTapes (input result row reversed pending : List HopRowSymbol) : Fin 6 → List HopRowSymbol :=
  ![input,[],result,row,reversed,pending]

private def hopRowCfg (label : Option HopRowLabel)
    (input result row reversed pending : List HopRowSymbol) : steinerUnaryHopMinimumRowFrameMachine.Cfg :=
  ⟨label,hopRowRegister none,hopRowTapes input result row reversed pending⟩

private theorem hopRowUpdate0 (a b c d e word : List HopRowSymbol) :
    Function.update (hopRowTapes a b c d e) 0 word = hopRowTapes word b c d e := by
  funext i
  fin_cases i <;> simp [hopRowTapes,Function.update]

private theorem hopRowUpdate2 (a b c d e word : List HopRowSymbol) :
    Function.update (hopRowTapes a b c d e) 2 word = hopRowTapes a word c d e := by
  funext i
  fin_cases i <;> simp [hopRowTapes,Function.update]

private theorem hopRowUpdate3 (a b c d e word : List HopRowSymbol) :
    Function.update (hopRowTapes a b c d e) 3 word = hopRowTapes a b word d e := by
  funext i
  fin_cases i <;> simp [hopRowTapes,Function.update]

private theorem hopRowUpdate4 (a b c d e word : List HopRowSymbol) :
    Function.update (hopRowTapes a b c d e) 4 word = hopRowTapes a b c word e := by
  funext i
  fin_cases i <;> simp [hopRowTapes,Function.update]

private theorem hopRowUpdate5 (a b c d e word : List HopRowSymbol) :
    Function.update (hopRowTapes a b c d e) 5 word = hopRowTapes a b c d word := by
  funext i
  fin_cases i <;> simp [hopRowTapes,Function.update]

private abbrev HopRowRun (before after : steinerUnaryHopMinimumRowFrameMachine.Cfg) (time : ℕ) :=
  EvalsToInTime steinerUnaryHopMinimumRowFrameMachine.step before (some after) time

private def hopRowOne {a b : steinerUnaryHopMinimumRowFrameMachine.Cfg}
    (step : steinerUnaryHopMinimumRowFrameMachine.step a = some b) : HopRowRun a b 1 := ⟨⟨1,step⟩,le_rfl⟩

private def hopRowThen {a b c : steinerUnaryHopMinimumRowFrameMachine.Cfg} {x y : ℕ}
    (first : HopRowRun a b x) (second : HopRowRun b c y) : HopRowRun a c (x+y) := by
  simpa only [Nat.add_comm] using EvalsToInTime.trans _ _ _ _ _ _ first second

private def hopRowRelax {a b : steinerUnaryHopMinimumRowFrameMachine.Cfg} {x y : ℕ}
    (run : HopRowRun a b x) (le : x ≤ y) : HopRowRun a b y := ⟨run.toEvalsTo,run.steps_le_m.trans le⟩

private theorem hopRowPrefix_push (word pending : List HopRowSymbol) :
    steinerUnaryHopMinimumRowFrameMachine.step (hopRowCfg (some .prefix) [] [] (hopRowTally::word) [] pending) =
      some (hopRowCfg (some .prefix) [] [] word [] (hopRowTally::pending)) := by
  simp only [FinTM2.step,steinerUnaryHopMinimumRowFrameMachine,hopRowCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopRowProgram,hopRowRead,hopRowSeen,hopRowNext,hopRowUpdate3,hopRowUpdate5]
  rfl

private theorem hopRowPrefix_end (word pending : List HopRowSymbol) :
    steinerUnaryHopMinimumRowFrameMachine.step (hopRowCfg (some .prefix) [] [] (hopRowField::word) [] pending) =
      some (hopRowCfg (some .cell) [] [] word [] (hopRowField::pending)) := by
  simp only [FinTM2.step,steinerUnaryHopMinimumRowFrameMachine,hopRowCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopRowProgram,hopRowRead,hopRowSeen,hopRowNext,hopRowUpdate3,hopRowUpdate5]
  rfl

private def hopRowPrefix (cap : ℕ) (word pending : List HopRowSymbol) :
    HopRowRun (hopRowCfg (some .prefix) [] [] (List.replicate cap hopRowTally++hopRowField::word) [] pending)
      (hopRowCfg (some .cell) [] [] word [] (hopRowField::(List.replicate cap hopRowTally++pending))) (cap+1) := by
  induction cap generalizing pending with
  | zero => exact hopRowOne (hopRowPrefix_end _ _)
  | succ cap ih =>
    have run := hopRowThen (hopRowOne (hopRowPrefix_push _ pending)) (ih (hopRowTally::pending))
    have saved : List.replicate cap hopRowTally++hopRowTally::pending = List.replicate (cap+1) hopRowTally++pending := by
      rw [List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [saved] at run
    exact hopRowRelax run (by omega)

private theorem hopRowCell_push (symbol : HopRowSymbol) (legal : symbol ≠ hopRowCell)
    (rest reversed pending : List HopRowSymbol) :
    steinerUnaryHopMinimumRowFrameMachine.step (hopRowCfg (some .cell) [] [] (symbol::rest) reversed pending) =
      some (hopRowCfg (some .cell) [] [] rest (symbol::reversed) pending) := by
  have check : ((some symbol : Option HopRowSymbol) == some hopRowCell) = false := by
    rcases symbol with b | value
    · cases b
      · exact (legal rfl).elim
      · rfl
    · rfl
  simp only [FinTM2.step,steinerUnaryHopMinimumRowFrameMachine,hopRowCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopRowProgram,hopRowRead,hopRowSeen,hopRowNext,hopRowUpdate3,hopRowUpdate4]
  change some (bif some symbol == some hopRowCell then hopRowCfg (some (.move .restore)) [] [] rest reversed pending
    else hopRowCfg (some .cell) [] [] rest (symbol::reversed) pending) = _
  rw [check]
  rfl

private theorem hopRowCell_end (rest reversed pending : List HopRowSymbol) :
    steinerUnaryHopMinimumRowFrameMachine.step (hopRowCfg (some .cell) [] [] (hopRowCell::rest) reversed pending) =
      some (hopRowCfg (some (.move .restore)) [] [] rest reversed pending) := by
  simp only [FinTM2.step,steinerUnaryHopMinimumRowFrameMachine,hopRowCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopRowProgram,hopRowRead,hopRowSeen,hopRowNext,hopRowUpdate3]
  rfl

private def hopRowReadCell (word rest reversed pending : List HopRowSymbol) (legal : hopRowCell ∉ word) :
    HopRowRun (hopRowCfg (some .cell) [] [] (word++hopRowCell::rest) reversed pending)
      (hopRowCfg (some (.move .restore)) [] [] rest (word.reverse++reversed) pending) (word.length+1) := by
  induction word generalizing reversed with
  | nil => exact hopRowOne (hopRowCell_end _ _ _)
  | cons symbol word ih =>
    simp only [List.mem_cons,not_or] at legal
    have run := hopRowThen (hopRowOne (hopRowCell_push symbol (Ne.symm legal.1) _ reversed pending))
      (ih (symbol::reversed) legal.2)
    simpa only [List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,List.nil_append,List.length_cons,
      Nat.add_left_comm,Nat.add_assoc] using run

private theorem hopRowCell_eof (pending : List HopRowSymbol) :
    steinerUnaryHopMinimumRowFrameMachine.step (hopRowCfg (some .cell) [] [] [] [] pending) =
      some (hopRowCfg (some (.move .finish)) [] [] [] [] pending) := by
  simp only [FinTM2.step,steinerUnaryHopMinimumRowFrameMachine,hopRowCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopRowProgram,hopRowRead,hopRowSeen,hopRowNext,hopRowUpdate3]
  rfl

private def hopRowMoveCfg (label : Option HopRowLabel) : HopRowMove →
    List HopRowSymbol → List HopRowSymbol → List HopRowSymbol → List HopRowSymbol →
      steinerUnaryHopMinimumRowFrameMachine.Cfg
  | .restore,src,dst,row,other => hopRowCfg label dst [] row src other
  | .archive,src,dst,row,other => hopRowCfg label [] src row other dst
  | .finish,src,dst,row,other => hopRowCfg label dst [] row other src

private def hopRowMoveReturn : HopRowMove → Option HopRowLabel
  | .restore => some hopRowCandidateStart
  | .archive => some .cell
  | .finish => none

private def hopRowMoveWord : HopRowMove → List HopRowSymbol → List HopRowSymbol
  | .archive,word => hopRowField::word
  | _,word => word

private theorem hopRowMove_push (phase : HopRowMove) (symbol : HopRowSymbol) (src dst row other : List HopRowSymbol) :
    steinerUnaryHopMinimumRowFrameMachine.step (hopRowMoveCfg (some (.move phase)) phase (symbol::src) dst row other) =
      some (hopRowMoveCfg (some (.move phase)) phase src (symbol::dst) row other) := by
  cases phase <;> simp only [hopRowMoveCfg,FinTM2.step,steinerUnaryHopMinimumRowFrameMachine,hopRowCfg,Turing.TM2.step,
    Turing.TM2.stepAux,hopRowProgram,hopRowRead,hopRowSeen,hopRowNext,hopRowMoveSource,hopRowMoveDestination,
    hopRowUpdate0,hopRowUpdate2,hopRowUpdate4,hopRowUpdate5] <;> rfl

private theorem hopRowMove_end (phase : HopRowMove) (dst row other : List HopRowSymbol) :
    steinerUnaryHopMinimumRowFrameMachine.step (hopRowMoveCfg (some (.move phase)) phase [] dst row other) =
      some (hopRowMoveCfg (hopRowMoveReturn phase) phase [] (hopRowMoveWord phase dst) row other) := by
  cases phase <;> simp only [hopRowMoveCfg,FinTM2.step,steinerUnaryHopMinimumRowFrameMachine,hopRowCfg,Turing.TM2.step,
    Turing.TM2.stepAux,hopRowProgram,hopRowRead,hopRowSeen,hopRowNext,hopRowMoveSource,hopRowMoveDestination,
    hopRowUpdate2,hopRowUpdate4,hopRowUpdate5,hopRowMoveEnd,hopRowMoveReturn,hopRowMoveWord] <;> rfl

private def hopRowMove (phase : HopRowMove) (source destination row other : List HopRowSymbol) :
    HopRowRun (hopRowMoveCfg (some (.move phase)) phase source destination row other)
      (hopRowMoveCfg (hopRowMoveReturn phase) phase [] (hopRowMoveWord phase (source.reverse++destination)) row other)
      (source.length+1) := by
  induction source generalizing destination with
  | nil => exact hopRowOne (hopRowMove_end _ _ _ _)
  | cons symbol source ih =>
    have run := hopRowThen (hopRowOne (hopRowMove_push phase symbol source destination row other)) (ih (symbol::destination))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,Nat.add_assoc,
      Nat.add_left_comm] using run

private noncomputable def hopRowCandidateHosted (row pending : List HopRowSymbol)
    (c : steinerUnaryHopTransferCandidateMachine.Cfg) : steinerUnaryHopMinimumRowFrameMachine.Cfg :=
  StackIndexEmbedding.configuration hopRowSlots (hopRowTapes [] [] row [] pending)
    (hopRowTag.returningConfiguration (.move .archive) c)

private theorem hopRowCandidate_step (row pending : List HopRowSymbol)
    {c after : steinerUnaryHopTransferCandidateMachine.Cfg}
    (move : steinerUnaryHopTransferCandidateMachine.step c = some after) :
    steinerUnaryHopMinimumRowFrameMachine.step (hopRowCandidateHosted row pending c) =
      some (hopRowCandidateHosted row pending after) := by
  have tagged := hopRowTag.step_embedded_return (HopRowLabel.move .archive)
    (base := steinerUnaryHopTransferCandidateMachine.m) (host := hopRowCandidateCode) (fun _ => rfl) move
  have hosted := StackIndexEmbedding.step_on hopRowSlots (base := hopRowCandidateCode)
    (hopRowTapes [] [] row [] pending) (hopRowTag.returningConfiguration (.move .archive) c)
  rw [tagged] at hosted
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact hosted

private theorem hopRowCandidate_tapes (c : steinerUnaryHopTransferCandidateMachine.Cfg)
    (input result row pending : List HopRowSymbol) (tapes : c.stk = ![input,[],result]) :
    (hopRowCandidateHosted row pending c).stk = hopRowTapes input result row [] pending := by
  have image (i : Fin 3) : (hopRowCandidateHosted row pending c).stk (hopRowSlots i) =
      (![input,[],result] : Fin 3 → List HopRowSymbol) i := by
    change StackIndexEmbedding.tapesAt hopRowSlots (fun j => (c.stk j).map id)
      (hopRowTapes [] [] row [] pending) (hopRowSlots i) = _
    rw [StackIndexEmbedding.tapesAt_image,List.map_id,tapes]
  have extra (i : Fin 6) (outside : ∀ j, hopRowSlots j ≠ i) :
      (hopRowCandidateHosted row pending c).stk i = hopRowTapes [] [] row [] pending i := by
    change StackIndexEmbedding.tapesAt hopRowSlots (fun j => (c.stk j).map id)
      (hopRowTapes [] [] row [] pending) i = _
    exact StackIndexEmbedding.tapesAt_extra hopRowSlots _ _ outside
  funext i
  fin_cases i
  · exact image 0
  · exact image 1
  · exact image 2
  · exact extra 3 (by intro j; fin_cases j <;> decide)
  · exact extra 4 (by intro j; fin_cases j <;> decide)
  · exact extra 5 (by intro j; fin_cases j <;> decide)

private theorem hopRowCandidate_init (input row pending : List HopRowSymbol) :
    hopRowCandidateHosted row pending (initList steinerUnaryHopTransferCandidateMachine input) =
      hopRowCfg (some hopRowCandidateStart) input [] row [] pending := by
  apply congrArg (fun tapes : Fin 6 → List HopRowSymbol =>
    (⟨some hopRowCandidateStart,hopRowRegister none,tapes⟩ : steinerUnaryHopMinimumRowFrameMachine.Cfg))
  apply hopRowCandidate_tapes
  funext i
  fin_cases i <;> rfl

private theorem hopRowCandidate_halt (result row pending : List HopRowSymbol) :
    hopRowCandidateHosted row pending (haltList steinerUnaryHopTransferCandidateMachine result) =
      hopRowCfg (some (.move .archive)) [] result row [] pending := by
  apply congrArg (fun tapes : Fin 6 → List HopRowSymbol =>
    (⟨some (.move .archive),hopRowRegister none,tapes⟩ : steinerUnaryHopMinimumRowFrameMachine.Cfg))
  apply hopRowCandidate_tapes
  funext i
  fin_cases i <;> rfl

private def hopRowValue (cap : ℕ) (cell : ℕ × ℕ) : ℕ := if cell.1 ≤ 1 then cell.2+cell.1 else cap

private def hopRowCellWord (cap : ℕ) (cell : ℕ × ℕ) : List HopRowSymbol :=
  encodeSteinerUnaryHopTransferCandidate (cap,cell.1,cell.2)

private noncomputable def hopRowCandidateRun (cap : ℕ) (cell : ℕ × ℕ) (row pending : List HopRowSymbol) :
    let word := hopRowCellWord cap cell
    let output := encodeSteinerUnaryRoundTotal (hopRowValue cap cell)
    HopRowRun (hopRowCfg (some hopRowCandidateStart) word [] row [] pending)
      (hopRowCfg (some (.move .archive)) [] output row [] pending) (2*word.length) := by
  let run := steinerUnaryHopTransferCandidateMachine_run cap cell.1 cell.2
  have executed := iterate_map_some (hopRowCandidateHosted row pending) (fun move => hopRowCandidate_step row pending move)
    run.steps run.evals_in_steps
  rw [hopRowCandidate_init,hopRowCandidate_halt] at executed
  exact ⟨⟨run.steps,executed⟩,run.steps_le_m⟩

private theorem hopRowCellWord_legal (cap : ℕ) (cell : ℕ × ℕ) : hopRowCell ∉ hopRowCellWord cap cell := by
  simp [hopRowCellWord,hopRowCell,encodeSteinerUnaryHopTransferCandidate,encodeSteinerUnaryRoundPriorVector,
    List.mem_replicate]

private theorem hopRowValue_le (cap : ℕ) (cell : ℕ × ℕ) : hopRowValue cap cell ≤ (hopRowCellWord cap cell).length := by
  rw [hopRowCellWord,encodeSteinerUnaryHopTransferCandidate_length]
  unfold hopRowValue
  split <;> omega

private theorem hopRowField_cons (value : ℕ) (values : List ℕ) :
    encodeSteinerUnaryRoundPriorVector (value::values) =
      (encodeSteinerUnaryRoundTotal value++[hopRowField])++encodeSteinerUnaryRoundPriorVector values := rfl

private theorem hopRowField_single (value : ℕ) :
    encodeSteinerUnaryRoundPriorVector [value] = encodeSteinerUnaryRoundTotal value++[hopRowField] := by
  rw [hopRowField_cons]
  exact List.append_nil _

private noncomputable def hopRowOneCell (cap : ℕ) (cell : ℕ × ℕ) (row pending : List HopRowSymbol) :
    let input := hopRowCellWord cap cell
    let output := encodeSteinerUnaryRoundPriorVector [hopRowValue cap cell]
    HopRowRun (hopRowCfg (some .cell) [] [] (input++hopRowCell::row) [] pending)
      (hopRowCfg (some .cell) [] [] row [] (output.reverse++pending)) (5*(input.length+1)) := by
  let input := hopRowCellWord cap cell
  let result := encodeSteinerUnaryRoundTotal (hopRowValue cap cell)
  have loaded := hopRowReadCell input row [] pending (hopRowCellWord_legal cap cell)
  rw [List.append_nil] at loaded
  have restored := hopRowMove .restore input.reverse [] row pending
  simp only [hopRowMoveCfg,hopRowMoveReturn,hopRowMoveWord,List.reverse_reverse,List.append_nil,List.length_reverse] at restored
  have computed := hopRowCandidateRun cap cell row pending
  have archived := hopRowMove .archive result pending row []
  simp only [hopRowMoveCfg,hopRowMoveReturn,hopRowMoveWord] at archived
  have shape : hopRowField::(result.reverse++pending) =
      (encodeSteinerUnaryRoundPriorVector [hopRowValue cap cell]).reverse++pending := by
    rw [hopRowField_single,List.reverse_append,List.reverse_singleton,List.append_assoc,List.singleton_append]
  rw [shape] at archived
  have run := hopRowThen (hopRowThen (hopRowThen loaded restored) computed) archived
  have value := hopRowValue_le cap cell
  refine hopRowRelax run ?_
  change _ ≤ 5*(input.length+1)
  change hopRowValue cap cell ≤ input.length at value
  dsimp only [result,input,encodeSteinerUnaryRoundTotal]
  simp only [List.length_replicate]
  dsimp only [input] at value
  omega

private def hopRowCellWords (cap : ℕ) (cells : List (ℕ × ℕ)) : List HopRowSymbol :=
  cells.flatMap fun cell => hopRowCellWord cap cell++[hopRowCell]

private theorem hopRowCellWords_cons (cap : ℕ) (cell : ℕ × ℕ) (cells : List (ℕ × ℕ)) :
    hopRowCellWords cap (cell::cells) = hopRowCellWord cap cell++hopRowCell::hopRowCellWords cap cells := by
  simp only [hopRowCellWords,List.flatMap_cons,List.append_assoc,List.singleton_append]

private noncomputable def hopRowAllCells (cap : ℕ) (cells : List (ℕ × ℕ)) (pending : List HopRowSymbol) :
    let input := hopRowCellWords cap cells
    let fields := encodeSteinerUnaryRoundPriorVector (cells.map (hopRowValue cap))
    HopRowRun (hopRowCfg (some .cell) [] [] input [] pending)
      (hopRowCfg (some (.move .finish)) [] [] [] [] (fields.reverse++pending)) (5*input.length+1) := by
  induction cells generalizing pending with
  | nil => exact hopRowOne (hopRowCell_eof pending)
  | cons cell cells ih =>
    dsimp only
    rw [hopRowCellWords_cons,List.map_cons,hopRowField_cons,← hopRowField_single,List.reverse_append,List.append_assoc]
    have first := hopRowOneCell cap cell (hopRowCellWords cap cells) pending
    have later := ih ((encodeSteinerUnaryRoundPriorVector [hopRowValue cap cell]).reverse++pending)
    have run := hopRowThen first later
    refine hopRowRelax run ?_
    simp only [List.length_append,List.length_cons]
    omega

/-- Supply one initial cap and one fully framed candidate request per cell. -/
def encodeSteinerUnaryHopMinimumRowFrame (request : ℕ × List (ℕ × ℕ)) : List SteinerUnaryCappedRowsSymbol :=
  encodeSteinerUnaryRoundPriorVector [request.1]++hopRowCellWords request.1 request.2

/-- The candidate words are ready for the native minimum machine. -/
def steinerUnaryHopMinimumRowFrameAnswer (request : ℕ × List (ℕ × ℕ)) : List SteinerUnaryCappedRowsSymbol :=
  encodeSteinerUnaryMinimum (request.1,request.2.map (hopRowValue request.1))

private theorem hopRowAnswer_length_le (cap : ℕ) (cells : List (ℕ × ℕ)) :
    (encodeSteinerUnaryRoundPriorVector (cells.map (hopRowValue cap))).length ≤ (hopRowCellWords cap cells).length := by
  induction cells with
  | nil => exact le_rfl
  | cons cell cells ih =>
    have val := hopRowValue_le cap cell
    simp only [List.map_cons,hopRowField_cons,hopRowCellWords_cons,List.length_append,List.length_nil,List.length_cons,
      encodeSteinerUnaryRoundTotal,List.length_replicate]
    omega

/-- The prepared minimum request fits in the supplied expanded frame. -/
theorem steinerUnaryHopMinimumRowFrameAnswer_length_le (request : ℕ × List (ℕ × ℕ)) :
    (steinerUnaryHopMinimumRowFrameAnswer request).length ≤ (encodeSteinerUnaryHopMinimumRowFrame request).length := by
  rcases request with ⟨cap,cells⟩
  change (encodeSteinerUnaryRoundPriorVector (cap::cells.map (hopRowValue cap))).length ≤
    (encodeSteinerUnaryRoundPriorVector [cap]++hopRowCellWords cap cells).length
  rw [hopRowField_cons,← hopRowField_single]
  simp only [List.length_append]
  exact Nat.add_le_add_left (hopRowAnswer_length_le cap cells) _

private theorem hopRowInit (word : List HopRowSymbol) :
    initList steinerUnaryHopMinimumRowFrameMachine word = hopRowCfg (some .prefix) [] [] word [] [] := by
  apply congrArg (fun tapes : Fin 6 → List HopRowSymbol =>
    (⟨some .prefix,hopRowRegister none,tapes⟩ : steinerUnaryHopMinimumRowFrameMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem hopRowHalt (word : List HopRowSymbol) :
    haltList steinerUnaryHopMinimumRowFrameMachine word = hopRowCfg none word [] [] [] [] := by
  apply congrArg (fun tapes : Fin 6 → List HopRowSymbol =>
    (⟨none,hopRowRegister none,tapes⟩ : steinerUnaryHopMinimumRowFrameMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- Compute the entire minimum request from the supplied expanded
row. The preparation time is linear in the unary input length. -/
noncomputable def steinerUnaryHopMinimumRowFrameMachine_run (request : ℕ × List (ℕ × ℕ)) :
    let input := encodeSteinerUnaryHopMinimumRowFrame request
    TM2OutputsInTime steinerUnaryHopMinimumRowFrameMachine input
      (some (steinerUnaryHopMinimumRowFrameAnswer request)) (6*input.length+2) := by
  rcases request with ⟨cap,cells⟩
  let row := hopRowCellWords cap cells
  let header := encodeSteinerUnaryRoundPriorVector [cap]
  let tail := encodeSteinerUnaryRoundPriorVector (cells.map (hopRowValue cap))
  let input := encodeSteinerUnaryHopMinimumRowFrame (cap,cells)
  have preparedHeader := hopRowPrefix cap row []
  rw [List.append_nil] at preparedHeader
  have tallies : encodeSteinerUnaryRoundTotal cap = List.replicate cap hopRowTally := rfl
  have front : header.reverse = hopRowField::List.replicate cap hopRowTally := by
    rw [show header = _ from hopRowField_single cap,tallies,List.reverse_append,List.reverse_singleton,
      List.singleton_append,List.reverse_replicate]
  have whole : input = List.replicate cap hopRowTally++hopRowField::row := by
    change header++row = _
    rw [show header = _ from hopRowField_single cap,List.append_assoc,List.singleton_append]
    rfl
  rw [← front,← whole] at preparedHeader
  have read := hopRowAllCells cap cells header.reverse
  have output : steinerUnaryHopMinimumRowFrameAnswer (cap,cells) = header++tail := by
    change encodeSteinerUnaryRoundPriorVector (cap::cells.map (hopRowValue cap)) = _
    rw [hopRowField_cons,show header = _ from hopRowField_single cap]
  have reverseOutput : tail.reverse++header.reverse = (header++tail).reverse := List.reverse_append.symm
  dsimp only at read
  change HopRowRun (hopRowCfg (some .cell) [] [] row [] header.reverse)
    (hopRowCfg (some (.move .finish)) [] [] [] [] (tail.reverse++header.reverse)) _ at read
  rw [reverseOutput,← output] at read
  have finish := hopRowMove .finish (tail.reverse++header.reverse) [] [] []
  rw [reverseOutput,← output] at finish
  simp only [hopRowMoveCfg,hopRowMoveReturn,hopRowMoveWord,List.reverse_reverse,List.length_reverse,List.append_nil] at finish
  have run := hopRowThen (hopRowThen preparedHeader read) finish
  change HopRowRun (initList steinerUnaryHopMinimumRowFrameMachine input) (haltList steinerUnaryHopMinimumRowFrameMachine _) _
  rw [hopRowInit,hopRowHalt]
  refine hopRowRelax run ?_
  have length : input.length = cap+1+row.length := by
    rw [whole]
    simp only [List.length_append,List.length_replicate,List.length_cons]
    omega
  have outputLen : (steinerUnaryHopMinimumRowFrameAnswer (cap,cells)).length ≤ input.length :=
    steinerUnaryHopMinimumRowFrameAnswer_length_le (cap,cells)
  change cap+1+(5*row.length+1)+((steinerUnaryHopMinimumRowFrameAnswer (cap,cells)).length+1) ≤ 6*input.length+2
  omega

/-- The actual frame conversion is linear in the supplied expanded row. -/
noncomputable def steinerUnaryHopMinimumRowFrameMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryHopMinimumRowFrame id steinerUnaryHopMinimumRowFrameAnswer where
  tm := steinerUnaryHopMinimumRowFrameMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 6*Polynomial.X+Polynomial.C 2
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_X,
      Polynomial.eval_C] using steinerUnaryHopMinimumRowFrameMachine_run request

end OnlineReachabilityPreservers
