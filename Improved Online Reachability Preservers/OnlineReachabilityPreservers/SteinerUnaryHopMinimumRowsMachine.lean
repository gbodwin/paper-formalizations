import OnlineReachabilityPreservers.SteinerUnaryHopMinimumRowMachine
import OnlineReachabilityPreservers.SteinerUnaryHopSharedCapRowFramesMachine

/-! Run native minimum evaluation on each supplied expanded hop row. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev HopRowsSymbol := SteinerUnaryCappedRowsSymbol
private abbrev HopRowsBase := steinerUnaryHopMinimumRowMachine
private abbrev HopRowsBaseLabel := HopRowsBase.Λ
private abbrev HopRowsBaseRegister := HopRowsBase.σ
private instance : Fintype HopRowsBaseLabel := HopRowsBase.ΛFin

private inductive HopRowsLabel where
  | read | restore | row (label : HopRowsBaseLabel) | archive | finish
  deriving Fintype

private abbrev HopRowsRegister := Option HopRowsSymbol × HopRowsBaseRegister
private abbrev HopRowsProgram := StackMachineTag.Program (Fin 9) HopRowsSymbol HopRowsLabel HopRowsRegister

private def hopRowsInitial : HopRowsRegister := (none,HopRowsBase.initialState)
private def hopRowsMark : HopRowsSymbol := Sum.inl true
private def hopRowsSeen (r : HopRowsRegister) : HopRowsSymbol := r.1.getD hopRowsMark
private def hopRowsPop (slot : Fin 9) (code : HopRowsProgram) : HopRowsProgram :=
  pop slot (fun _ seen => (seen,HopRowsBase.initialState)) code
private def hopRowsNext (label : HopRowsLabel) : HopRowsProgram := load (fun _ => hopRowsInitial) (goto fun _ => label)

private def hopRowsTag :
    StackMachineTag HopRowsSymbol HopRowsSymbol HopRowsBaseLabel HopRowsLabel HopRowsBaseRegister HopRowsRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (none,r)
  readRegister := Prod.snd
  writeLabel := .row
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def hopRowsSlots : Fin 6 ↪ Fin 9 where
  toFun i := ⟨i.val,i.isLt.trans (by decide)⟩
  inj' := fun _ _ eq => Fin.ext (congrArg (Fin.val : Fin 9 → ℕ) eq)

private def hopRowsInner : HopRowsLabel → StackMachineTag.Program (Fin 6) HopRowsSymbol HopRowsLabel HopRowsRegister
  | .row label => hopRowsTag.returningStatement .archive (HopRowsBase.m label)
  | _ => halt

private def hopRowsStart : HopRowsLabel := .row HopRowsBase.main

private def hopRowsProgram : HopRowsLabel → HopRowsProgram
  | .read => hopRowsPop 6 <| branch (fun r => r.1.isSome)
      (branch (fun r => r.1 == some hopRowsMark)
        (hopRowsNext .restore) (push 7 hopRowsSeen (hopRowsNext .read)))
      (hopRowsNext .finish)
  | .restore => hopRowsPop 7 <| branch (fun r => r.1.isSome)
      (push 3 hopRowsSeen (hopRowsNext .restore)) (hopRowsNext hopRowsStart)
  | .row label => StackIndexEmbedding.statement hopRowsSlots (hopRowsInner (.row label))
  | .archive => hopRowsPop 3 <| branch (fun r => r.1.isSome)
      (push 8 hopRowsSeen (hopRowsNext .archive)) (push 8 (fun _ => hopRowsMark) (hopRowsNext .read))
  | .finish => hopRowsPop 8 <| branch (fun r => r.1.isSome)
      (push 6 hopRowsSeen (hopRowsNext .finish)) (load (fun _ => hopRowsInitial) halt)

/-- Evaluate each delimited expanded row and collect its unary minimum.
The input tape is reused for the ordered sequence of minima. -/
abbrev steinerUnaryHopMinimumRowsMachine : FinTM2 where
  K := Fin 9
  k₀ := 6
  k₁ := 6
  Γ _ := HopRowsSymbol
  Λ := HopRowsLabel
  main := .read
  σ := HopRowsRegister
  initialState := hopRowsInitial
  m := hopRowsProgram

private def hopRowsTapes (row input work output : List HopRowsSymbol) : Fin 9 → List HopRowsSymbol :=
  ![[],[],[],row,[],[],input,work,output]

private def hopRowsCfg (label : Option HopRowsLabel) (row input work output : List HopRowsSymbol) :
    steinerUnaryHopMinimumRowsMachine.Cfg := ⟨label,hopRowsInitial,hopRowsTapes row input work output⟩

private theorem hopRowsUpdate3 (r i w o v : List HopRowsSymbol) :
    Function.update (hopRowsTapes r i w o) 3 v = hopRowsTapes v i w o := by
  funext slot
  fin_cases slot <;> simp [hopRowsTapes,Function.update]

private theorem hopRowsUpdate6 (r i w o v : List HopRowsSymbol) :
    Function.update (hopRowsTapes r i w o) 6 v = hopRowsTapes r v w o := by
  funext slot
  fin_cases slot <;> simp [hopRowsTapes,Function.update]

private theorem hopRowsUpdate7 (r i w o v : List HopRowsSymbol) :
    Function.update (hopRowsTapes r i w o) 7 v = hopRowsTapes r i v o := by
  funext slot
  fin_cases slot <;> simp [hopRowsTapes,Function.update]

private theorem hopRowsUpdate8 (r i w o v : List HopRowsSymbol) :
    Function.update (hopRowsTapes r i w o) 8 v = hopRowsTapes r i w v := by
  funext slot
  fin_cases slot <;> simp [hopRowsTapes,Function.update]

private abbrev HopRowsRun (a b : steinerUnaryHopMinimumRowsMachine.Cfg) (time : ℕ) :=
  EvalsToInTime steinerUnaryHopMinimumRowsMachine.step a (some b) time

private def hopRowsOne {a b : steinerUnaryHopMinimumRowsMachine.Cfg}
    (move : steinerUnaryHopMinimumRowsMachine.step a = some b) : HopRowsRun a b 1 := ⟨⟨1,move⟩,le_rfl⟩

private def hopRowsThen {a b c : steinerUnaryHopMinimumRowsMachine.Cfg} {x y : ℕ}
    (first : HopRowsRun a b x) (second : HopRowsRun b c y) : HopRowsRun a c (x+y) := by
  simpa only [Nat.add_comm] using EvalsToInTime.trans _ _ _ _ _ _ first second

private def hopRowsRelax {a b : steinerUnaryHopMinimumRowsMachine.Cfg} {x y : ℕ}
    (run : HopRowsRun a b x) (bound : x ≤ y) : HopRowsRun a b y :=
  ⟨run.toEvalsTo,run.steps_le_m.trans bound⟩

private theorem hopRowsRead_push (symbol : HopRowsSymbol) (legal : symbol ≠ hopRowsMark) (i w o : List HopRowsSymbol) :
    steinerUnaryHopMinimumRowsMachine.step (hopRowsCfg (some .read) [] (symbol::i) w o) =
      some (hopRowsCfg (some .read) [] i (symbol::w) o) := by
  have check : ((some symbol : Option HopRowsSymbol) == some hopRowsMark) = false := by
    rcases symbol with b | b
    · cases b
      · rfl
      · exact (legal rfl).elim
    · rfl
  simp only [FinTM2.step,steinerUnaryHopMinimumRowsMachine,hopRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopRowsProgram,hopRowsPop,hopRowsSeen,hopRowsNext,hopRowsUpdate6,hopRowsUpdate7]
  change some (bif some symbol == some hopRowsMark then hopRowsCfg (some .restore) [] i w o
    else hopRowsCfg (some .read) [] i (symbol::w) o) = _
  rw [check]
  rfl

private theorem hopRowsRead_mark (i w o : List HopRowsSymbol) :
    steinerUnaryHopMinimumRowsMachine.step (hopRowsCfg (some .read) [] (hopRowsMark::i) w o) =
      some (hopRowsCfg (some .restore) [] i w o) := by
  simp only [FinTM2.step,steinerUnaryHopMinimumRowsMachine,hopRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopRowsProgram,hopRowsPop,hopRowsNext,hopRowsUpdate6]
  rfl

private def hopRowsRead (word i w o : List HopRowsSymbol) (legal : hopRowsMark ∉ word) :
    HopRowsRun (hopRowsCfg (some .read) [] (word++hopRowsMark::i) w o)
      (hopRowsCfg (some .restore) [] i (word.reverse++w) o) (word.length+1) := by
  induction word generalizing w with
  | nil => exact hopRowsOne (hopRowsRead_mark i w o)
  | cons symbol word ih =>
    rw [List.mem_cons,not_or] at legal
    have first := hopRowsOne (hopRowsRead_push symbol (Ne.symm legal.1) (word++hopRowsMark::i) w o)
    have run := hopRowsThen first (ih (symbol::w) legal.2)
    simpa only [List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,List.nil_append,
      List.length_cons,Nat.add_assoc,Nat.add_left_comm] using run

private theorem hopRowsRestore_push (symbol : HopRowsSymbol) (r i w o : List HopRowsSymbol) :
    steinerUnaryHopMinimumRowsMachine.step (hopRowsCfg (some .restore) r i (symbol::w) o) =
      some (hopRowsCfg (some .restore) (symbol::r) i w o) := by
  simp only [FinTM2.step,steinerUnaryHopMinimumRowsMachine,hopRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopRowsProgram,hopRowsPop,hopRowsSeen,hopRowsNext,hopRowsUpdate7,hopRowsUpdate3]
  rfl

private theorem hopRowsRestore_end (r i o : List HopRowsSymbol) :
    steinerUnaryHopMinimumRowsMachine.step (hopRowsCfg (some .restore) r i [] o) =
      some (hopRowsCfg (some hopRowsStart) r i [] o) := by
  simp only [FinTM2.step,steinerUnaryHopMinimumRowsMachine,hopRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopRowsProgram,hopRowsPop,hopRowsNext,hopRowsUpdate7]
  rfl

private def hopRowsRestore (r i w o : List HopRowsSymbol) :
    HopRowsRun (hopRowsCfg (some .restore) r i w o)
      (hopRowsCfg (some hopRowsStart) (w.reverse++r) i [] o) (w.length+1) := by
  induction w generalizing r with
  | nil => exact hopRowsOne (hopRowsRestore_end r i o)
  | cons symbol w ih =>
    have run := hopRowsThen (hopRowsOne (hopRowsRestore_push symbol r i w o)) (ih (symbol::r))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_left_comm,List.length_cons] using run

private def hopRowsPassive (i o : List HopRowsSymbol) (slot : Fin 9) : List HopRowsSymbol :=
  if slot = 6 then i else if slot = 8 then o else []

private noncomputable def hopRowsHosted (i o : List HopRowsSymbol) (c : HopRowsBase.Cfg) : steinerUnaryHopMinimumRowsMachine.Cfg :=
  StackIndexEmbedding.configuration hopRowsSlots (hopRowsPassive i o) (hopRowsTag.returningConfiguration .archive c)

private theorem hopRowsRow_step (i o : List HopRowsSymbol) {a b : HopRowsBase.Cfg} (move : HopRowsBase.step a = some b) :
    steinerUnaryHopMinimumRowsMachine.step (hopRowsHosted i o a) = some (hopRowsHosted i o b) := by
  have tagged := hopRowsTag.step_embedded_return .archive (base := HopRowsBase.m) (host := hopRowsInner) (fun _ => rfl) move
  have hosted := StackIndexEmbedding.step_on hopRowsSlots (base := hopRowsInner) (hopRowsPassive i o)
    (hopRowsTag.returningConfiguration .archive a)
  rw [tagged] at hosted
  rcases a with ⟨label,register,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact hosted

private theorem hopRowsRow_tapes (i o word : List HopRowsSymbol) (c : HopRowsBase.Cfg)
    (shape : c.stk = ![[],[],[],word,[],[]]) : (hopRowsHosted i o c).stk = hopRowsTapes word i [] o := by
  have image (slot : Fin 6) : (hopRowsHosted i o c).stk (hopRowsSlots slot) =
      (![[],[],[],word,[],[]] : Fin 6 → List HopRowsSymbol) slot := by
    change StackIndexEmbedding.tapesAt hopRowsSlots (fun k => (c.stk k).map id)
      (hopRowsPassive i o) (hopRowsSlots slot) = _
    rw [StackIndexEmbedding.tapesAt_image,List.map_id,shape]
  have extra (slot : Fin 9) (absent : ∀ j, hopRowsSlots j ≠ slot) :
      (hopRowsHosted i o c).stk slot = hopRowsPassive i o slot :=
    StackIndexEmbedding.tapesAt_extra hopRowsSlots _ _ absent
  funext slot
  fin_cases slot
  · exact image 0
  · exact image 1
  · exact image 2
  · exact image 3
  · exact image 4
  · exact image 5
  · exact extra 6 (by intro j; fin_cases j <;> decide)
  · exact extra 7 (by intro j; fin_cases j <;> decide)
  · exact extra 8 (by intro j; fin_cases j <;> decide)

private theorem hopRowsRow_init (i o word : List HopRowsSymbol) :
    hopRowsHosted i o (initList HopRowsBase word) = hopRowsCfg (some hopRowsStart) word i [] o := by
  apply congrArg (fun stk : Fin 9 → List HopRowsSymbol =>
    (⟨some hopRowsStart,hopRowsInitial,stk⟩ : steinerUnaryHopMinimumRowsMachine.Cfg))
  apply hopRowsRow_tapes
  funext slot
  fin_cases slot <;> rfl

private theorem hopRowsRow_halt (i o word : List HopRowsSymbol) :
    hopRowsHosted i o (haltList HopRowsBase word) = hopRowsCfg (some .archive) word i [] o := by
  apply congrArg (fun stk : Fin 9 → List HopRowsSymbol =>
    (⟨some .archive,hopRowsInitial,stk⟩ : steinerUnaryHopMinimumRowsMachine.Cfg))
  apply hopRowsRow_tapes
  funext slot
  fin_cases slot <;> rfl

private noncomputable def hopRowsRow (request : ℕ × List (ℕ × ℕ)) (i o : List HopRowsSymbol) :
    let word := encodeSteinerUnaryHopMinimumRowFrame request
    let value := encodeSteinerUnaryRoundTotal (steinerUnaryHopMinimumRowValue request)
    HopRowsRun (hopRowsCfg (some hopRowsStart) word i [] o) (hopRowsCfg (some .archive) value i [] o) (8*word.length+3) := by
  let run := steinerUnaryHopMinimumRowMachine_run request
  have executed := iterate_map_some (hopRowsHosted i o) (fun move => hopRowsRow_step i o move)
    run.steps run.evals_in_steps
  rw [hopRowsRow_init,hopRowsRow_halt] at executed
  exact ⟨⟨run.steps,executed⟩,run.steps_le_m⟩

private theorem hopRowsArchive_push (symbol : HopRowsSymbol) (r i o : List HopRowsSymbol) :
    steinerUnaryHopMinimumRowsMachine.step (hopRowsCfg (some .archive) (symbol::r) i [] o) =
      some (hopRowsCfg (some .archive) r i [] (symbol::o)) := by
  simp only [FinTM2.step,steinerUnaryHopMinimumRowsMachine,hopRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopRowsProgram,hopRowsPop,hopRowsSeen,hopRowsNext,hopRowsUpdate3,hopRowsUpdate8]
  rfl

private theorem hopRowsArchive_end (i o : List HopRowsSymbol) :
    steinerUnaryHopMinimumRowsMachine.step (hopRowsCfg (some .archive) [] i [] o) =
      some (hopRowsCfg (some .read) [] i [] (hopRowsMark::o)) := by
  simp only [FinTM2.step,steinerUnaryHopMinimumRowsMachine,hopRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopRowsProgram,hopRowsPop,hopRowsNext,hopRowsUpdate3,hopRowsUpdate8]
  rfl

private def hopRowsArchive (word i o : List HopRowsSymbol) :
    HopRowsRun (hopRowsCfg (some .archive) word i [] o)
      (hopRowsCfg (some .read) [] i [] ((word++[hopRowsMark]).reverse++o)) (word.length+1) := by
  induction word generalizing o with
  | nil => exact hopRowsOne (hopRowsArchive_end i o)
  | cons symbol word ih =>
    have run := hopRowsThen (hopRowsOne (hopRowsArchive_push symbol word i o)) (ih (symbol::o))
    simpa only [List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,List.nil_append,List.length_cons,
      Nat.add_assoc,Nat.add_left_comm] using run

private theorem hopRowsRead_end (o : List HopRowsSymbol) :
    steinerUnaryHopMinimumRowsMachine.step (hopRowsCfg (some .read) [] [] [] o) =
      some (hopRowsCfg (some .finish) [] [] [] o) := by
  simp only [FinTM2.step,steinerUnaryHopMinimumRowsMachine,hopRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopRowsProgram,hopRowsPop,hopRowsNext,hopRowsUpdate6]
  rfl

private theorem hopRowsFinish_push (symbol : HopRowsSymbol) (i o : List HopRowsSymbol) :
    steinerUnaryHopMinimumRowsMachine.step (hopRowsCfg (some .finish) [] i [] (symbol::o)) =
      some (hopRowsCfg (some .finish) [] (symbol::i) [] o) := by
  simp only [FinTM2.step,steinerUnaryHopMinimumRowsMachine,hopRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopRowsProgram,hopRowsPop,hopRowsSeen,hopRowsNext,hopRowsUpdate8,hopRowsUpdate6]
  rfl

private theorem hopRowsFinish_end (i : List HopRowsSymbol) :
    steinerUnaryHopMinimumRowsMachine.step (hopRowsCfg (some .finish) [] i [] []) =
      some (hopRowsCfg none [] i [] []) := by
  simp only [FinTM2.step,steinerUnaryHopMinimumRowsMachine,hopRowsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopRowsProgram,hopRowsPop,hopRowsUpdate8]
  rfl

private def hopRowsFinish (i o : List HopRowsSymbol) :
    HopRowsRun (hopRowsCfg (some .finish) [] i [] o) (hopRowsCfg none [] (o.reverse++i) [] []) (o.length+1) := by
  induction o generalizing i with
  | nil => exact hopRowsOne (hopRowsFinish_end i)
  | cons symbol o ih =>
    have run := hopRowsThen (hopRowsOne (hopRowsFinish_push symbol i o)) (ih (symbol::i))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_left_comm,List.length_cons] using run

private theorem hopRowsWord_legal (cap : ℕ) (row : List (ℕ × ℕ)) :
    hopRowsMark ∉ encodeSteinerUnaryHopMinimumRowFrame (cap,row) := by
  change hopRowsMark ∉ encodeSteinerUnaryRoundPriorVector [cap]++row.flatMap (fun cell =>
    encodeSteinerUnaryHopTransferCandidate (cap,cell.1,cell.2)++[Sum.inl false])
  simp [hopRowsMark,encodeSteinerUnaryHopTransferCandidate,encodeSteinerUnaryRoundPriorVector,
    List.mem_flatMap,List.mem_replicate]

private theorem hopRowsWord_cap (cap : ℕ) (row : List (ℕ × ℕ)) :
    cap ≤ (encodeSteinerUnaryHopMinimumRowFrame (cap,row)).length := by
  simp [encodeSteinerUnaryHopMinimumRowFrame,encodeSteinerUnaryRoundPriorVector]

private theorem hopRowsValue_cap (cap : ℕ) (row : List (ℕ × ℕ)) :
    steinerUnaryHopMinimumRowValue (cap,row) ≤ cap := by
  unfold steinerUnaryHopMinimumRowValue
  generalize (List.map _ row) = values
  induction values generalizing cap with
  | nil => exact le_rfl
  | cons value values ih =>
    exact (ih (min cap value)).trans (min_le_left cap value)

private def hopRowsValueWord (cap : ℕ) (row : List (ℕ × ℕ)) : List HopRowsSymbol :=
  encodeSteinerUnaryRoundTotal (steinerUnaryHopMinimumRowValue (cap,row))

private theorem hopRowsValue_length (cap : ℕ) (row : List (ℕ × ℕ)) :
    (hopRowsValueWord cap row).length ≤ (encodeSteinerUnaryHopMinimumRowFrame (cap,row)).length := by
  rw [hopRowsValueWord,encodeSteinerUnaryRoundTotal,List.length_replicate]
  exact (hopRowsValue_cap cap row).trans (hopRowsWord_cap cap row)

/-- The unary minima, one per supplied row, in their original order. -/
def steinerUnaryHopMinimumRowsAnswer (request : SteinerUnarySharedCapRows) : List SteinerUnaryCappedRowsSymbol :=
  encodeSteinerUnaryCappedRowTallies (request.2.map fun row => steinerUnaryHopMinimumRowValue (request.1,row))

private theorem hopRowsAnswer_cons (cap : ℕ) (row : List (ℕ × ℕ)) (rows : List (List (ℕ × ℕ))) :
    steinerUnaryHopMinimumRowsAnswer (cap,row::rows) =
      (hopRowsValueWord cap row++[hopRowsMark])++steinerUnaryHopMinimumRowsAnswer (cap,rows) := rfl

private theorem hopRowsInput_cons (cap : ℕ) (row : List (ℕ × ℕ)) (rows : List (List (ℕ × ℕ))) :
    steinerUnaryHopSharedCapRowFramesAnswer (cap,row::rows) =
      (encodeSteinerUnaryHopMinimumRowFrame (cap,row)++[hopRowsMark])++steinerUnaryHopSharedCapRowFramesAnswer (cap,rows) := rfl

private noncomputable def hopRowsOneRow (cap : ℕ) (row : List (ℕ × ℕ)) (i o : List HopRowsSymbol) :
    let word := encodeSteinerUnaryHopMinimumRowFrame (cap,row)
    let value := hopRowsValueWord cap row
    HopRowsRun (hopRowsCfg (some .read) [] (word++hopRowsMark::i) [] o)
      (hopRowsCfg (some .read) [] i [] ((value++[hopRowsMark]).reverse++o)) (11*(word.length+1)) := by
  let word := encodeSteinerUnaryHopMinimumRowFrame (cap,row)
  let value := hopRowsValueWord cap row
  have read := hopRowsRead word i [] o (hopRowsWord_legal cap row)
  rw [List.append_nil] at read
  have retape := hopRowsRestore [] i word.reverse o
  rw [List.reverse_reverse,List.append_nil,List.length_reverse] at retape
  have rowRun := hopRowsRow (cap,row) i o
  have run := hopRowsThen (hopRowsThen (hopRowsThen read retape) rowRun) (hopRowsArchive value i o)
  refine hopRowsRelax run ?_
  have size : value.length ≤ word.length := hopRowsValue_length cap row
  change (word.length+1)+(word.length+1)+(8*word.length+3)+(value.length+1) ≤ 11*(word.length+1)
  omega

private noncomputable def hopRowsAll (cap : ℕ) (rows : List (List (ℕ × ℕ))) (out : List HopRowsSymbol) :
    let input := steinerUnaryHopSharedCapRowFramesAnswer (cap,rows)
    let answer := steinerUnaryHopMinimumRowsAnswer (cap,rows)
    HopRowsRun (hopRowsCfg (some .read) [] input [] out)
      (hopRowsCfg (some .finish) [] [] [] (answer.reverse++out)) (11*input.length+1) := by
  induction rows generalizing out with
  | nil => exact hopRowsOne (hopRowsRead_end out)
  | cons row rows ih =>
    dsimp only
    rw [hopRowsInput_cons,hopRowsAnswer_cons]
    let word := hopRowsValueWord cap row++[hopRowsMark]
    have first := hopRowsOneRow cap row (steinerUnaryHopSharedCapRowFramesAnswer (cap,rows)) out
    have rest := ih (word.reverse++out)
    have run := hopRowsThen first rest
    rw [List.append_assoc (encodeSteinerUnaryHopMinimumRowFrame (cap,row)) [hopRowsMark]
      (steinerUnaryHopSharedCapRowFramesAnswer (cap,rows)),List.singleton_append]
    change HopRowsRun (hopRowsCfg (some .read) [] (encodeSteinerUnaryHopMinimumRowFrame (cap,row)++
      hopRowsMark::steinerUnaryHopSharedCapRowFramesAnswer (cap,rows)) [] out)
      (hopRowsCfg (some .finish) [] [] [] ((word++steinerUnaryHopMinimumRowsAnswer (cap,rows)).reverse++out)) _
    rw [List.reverse_append,List.append_assoc (steinerUnaryHopMinimumRowsAnswer (cap,rows)).reverse word.reverse out]
    refine hopRowsRelax run ?_
    simp only [List.length_append,List.length_cons,Nat.mul_add,Nat.add_assoc]
    omega

/-- The unary minimum in each row fits inside its expanded input row. -/
theorem steinerUnaryHopMinimumRowsAnswer_length_le (request : SteinerUnarySharedCapRows) :
    (steinerUnaryHopMinimumRowsAnswer request).length ≤ (steinerUnaryHopSharedCapRowFramesAnswer request).length := by
  rcases request with ⟨cap,rows⟩
  induction rows with
  | nil => exact le_rfl
  | cons row rows ih =>
    rw [hopRowsInput_cons,hopRowsAnswer_cons]
    simp only [List.length_append,List.length_singleton]
    have one := hopRowsValue_length cap row
    omega

private theorem hopRows_init (word : List HopRowsSymbol) :
    initList steinerUnaryHopMinimumRowsMachine word = hopRowsCfg (some .read) [] word [] [] := by
  apply congrArg (fun stk : Fin 9 → List HopRowsSymbol =>
    (⟨some .read,hopRowsInitial,stk⟩ : steinerUnaryHopMinimumRowsMachine.Cfg))
  funext slot
  fin_cases slot <;> rfl

private theorem hopRows_halt (word : List HopRowsSymbol) :
    haltList steinerUnaryHopMinimumRowsMachine word = hopRowsCfg none [] word [] [] := by
  apply congrArg (fun stk : Fin 9 → List HopRowsSymbol =>
    (⟨none,hopRowsInitial,stk⟩ : steinerUnaryHopMinimumRowsMachine.Cfg))
  funext slot
  fin_cases slot <;> rfl

/-- Run every supplied expanded hop row in linear native time. -/
noncomputable def steinerUnaryHopMinimumRowsMachine_run (request : SteinerUnarySharedCapRows) :
    let input := steinerUnaryHopSharedCapRowFramesAnswer request
    TM2OutputsInTime steinerUnaryHopMinimumRowsMachine input (some (steinerUnaryHopMinimumRowsAnswer request)) (12*input.length+2) := by
  rcases request with ⟨cap,rows⟩
  let input := steinerUnaryHopSharedCapRowFramesAnswer (cap,rows)
  let answer := steinerUnaryHopMinimumRowsAnswer (cap,rows)
  have collected := hopRowsAll cap rows []
  simp only [List.append_nil] at collected
  have finish := hopRowsFinish [] answer.reverse
  rw [List.reverse_reverse,List.append_nil,List.length_reverse] at finish
  have run := hopRowsThen collected finish
  change HopRowsRun (initList steinerUnaryHopMinimumRowsMachine input) (haltList steinerUnaryHopMinimumRowsMachine answer) _
  rw [hopRows_init,hopRows_halt]
  refine hopRowsRelax run ?_
  have size : answer.length ≤ input.length := steinerUnaryHopMinimumRowsAnswer_length_le (cap,rows)
  change 11*input.length+1+(answer.length+1) ≤ 12*input.length+2
  omega

/-- The row loop has a linear transition polynomial in the expanded input. -/
noncomputable def steinerUnaryHopMinimumRowsMachine_polytime :
    TM2ComputableInPolyTime steinerUnaryHopSharedCapRowFramesAnswer id steinerUnaryHopMinimumRowsAnswer where
  tm := steinerUnaryHopMinimumRowsMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 12*Polynomial.X+Polynomial.C 2
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_C,
      Polynomial.eval_X] using steinerUnaryHopMinimumRowsMachine_run request

end OnlineReachabilityPreservers
