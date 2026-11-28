import OnlineReachabilityPreservers.SteinerUnaryHopMinimumRowFrameMachine
import OnlineReachabilityPreservers.SteinerUnarySharedCapRowsMachine

/-! Make expanded minimum-row requests from one shared sentinel. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev HopFramesSymbol := SteinerUnaryCappedRowsSymbol
private abbrev HopFramesRegister := Option HopFramesSymbol

private inductive HopFramesLabel where
  | readCap | row | cell
  | copyCap (header : Bool) | restoreCap (header : Bool)
  | copyCell | clear | finish
  deriving Fintype

private abbrev HopFramesProgram := StackMachineTag.Program (Fin 4) HopFramesSymbol HopFramesLabel HopFramesRegister

private def hopFramesTally : HopFramesSymbol := Sum.inr (some true)
private def hopFramesField : HopFramesSymbol := Sum.inr none
private def hopFramesCellMark : HopFramesSymbol := Sum.inl false
private def hopFramesRowMark : HopFramesSymbol := Sum.inl true

private def hopFramesRead (slot : Fin 4) (code : HopFramesProgram) : HopFramesProgram :=
  pop slot (fun _ seen => seen) code

private def hopFramesPeek (slot : Fin 4) (code : HopFramesProgram) : HopFramesProgram :=
  peek slot (fun _ seen => seen) code

private def hopFramesSeen (r : HopFramesRegister) : HopFramesSymbol := r.getD hopFramesCellMark

private def hopFramesNext (label : HopFramesLabel) : HopFramesProgram := load (fun _ => none) (goto fun _ => label)

private def hopFramesAfterCap : Bool → HopFramesLabel
  | true => .cell
  | false => .copyCell

private def hopFramesProgram : HopFramesLabel → HopFramesProgram
  | .readCap => hopFramesRead 0 <| branch (· == some hopFramesCellMark) (hopFramesNext .row)
      (push 1 hopFramesSeen (hopFramesNext .readCap))
  | .row => hopFramesPeek 0 <| branch Option.isSome (hopFramesNext (.copyCap true)) (hopFramesNext .clear)
  | .cell => hopFramesPeek 0 <| branch (· == some hopFramesRowMark)
      (hopFramesRead 0 (push 3 hopFramesSeen (hopFramesNext .row)))
      (hopFramesNext (.copyCap false))
  | .copyCap header => hopFramesRead 1 <| branch Option.isSome
      (push 2 hopFramesSeen <| push 3 hopFramesSeen (hopFramesNext (.copyCap header)))
      (push 3 (fun _ => hopFramesField) (hopFramesNext (.restoreCap header)))
  | .restoreCap header => hopFramesRead 2 <| branch Option.isSome
      (push 1 hopFramesSeen (hopFramesNext (.restoreCap header))) (hopFramesNext (hopFramesAfterCap header))
  | .copyCell => hopFramesRead 0 <| branch (· == some hopFramesCellMark)
      (push 3 (fun _ => hopFramesField) <| push 3 hopFramesSeen (hopFramesNext .cell))
      (push 3 hopFramesSeen (hopFramesNext .copyCell))
  | .clear => hopFramesRead 1 <| branch Option.isSome (hopFramesNext .clear) (hopFramesNext .finish)
  | .finish => hopFramesRead 3 <| branch Option.isSome
      (push 0 hopFramesSeen (hopFramesNext .finish)) (load (fun _ => none) halt)

/-- Keep one archived cap and expand it before each row and each cell.
Preserve the row markers so each minimum request can be run in turn. -/
abbrev steinerUnaryHopSharedCapRowFramesMachine : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 0
  Γ _ := HopFramesSymbol
  Λ := HopFramesLabel
  main := .readCap
  σ := HopFramesRegister
  initialState := none
  m := hopFramesProgram

private def hopFramesTapes (input cap work output : List HopFramesSymbol) : Fin 4 → List HopFramesSymbol :=
  ![input,cap,work,output]

private def hopFramesCfg (label : Option HopFramesLabel) (input cap work output : List HopFramesSymbol) :
    steinerUnaryHopSharedCapRowFramesMachine.Cfg := ⟨label,none,hopFramesTapes input cap work output⟩

private theorem hopFramesUpdate0 (i c w o payload : List HopFramesSymbol) :
    Function.update (hopFramesTapes i c w o) 0 payload = hopFramesTapes payload c w o := by
  funext slot
  fin_cases slot <;> simp [hopFramesTapes,Function.update]

private theorem hopFramesUpdate1 (i c w o payload : List HopFramesSymbol) :
    Function.update (hopFramesTapes i c w o) 1 payload = hopFramesTapes i payload w o := by
  funext slot
  fin_cases slot <;> simp [hopFramesTapes,Function.update]

private theorem hopFramesUpdate2 (i c w o payload : List HopFramesSymbol) :
    Function.update (hopFramesTapes i c w o) 2 payload = hopFramesTapes i c payload o := by
  funext slot
  fin_cases slot <;> simp [hopFramesTapes,Function.update]

private theorem hopFramesUpdate3 (i c w o payload : List HopFramesSymbol) :
    Function.update (hopFramesTapes i c w o) 3 payload = hopFramesTapes i c w payload := by
  funext slot
  fin_cases slot <;> simp [hopFramesTapes,Function.update]

private abbrev HopFramesRun (a b : steinerUnaryHopSharedCapRowFramesMachine.Cfg) (time : ℕ) :=
  EvalsToInTime steinerUnaryHopSharedCapRowFramesMachine.step a (some b) time

private def hopFramesOne {a b : steinerUnaryHopSharedCapRowFramesMachine.Cfg}
    (step : steinerUnaryHopSharedCapRowFramesMachine.step a = some b) : HopFramesRun a b 1 := ⟨⟨1,step⟩,le_rfl⟩

private def hopFramesThen {a b c : steinerUnaryHopSharedCapRowFramesMachine.Cfg} {x y : ℕ}
    (first : HopFramesRun a b x) (second : HopFramesRun b c y) : HopFramesRun a c (x+y) := by
  simpa only [Nat.add_comm] using EvalsToInTime.trans _ _ _ _ _ _ first second

private def hopFramesRelax {a b : steinerUnaryHopSharedCapRowFramesMachine.Cfg} {x y : ℕ}
    (run : HopFramesRun a b x) (le : x ≤ y) : HopFramesRun a b y := ⟨run.toEvalsTo,run.steps_le_m.trans le⟩

private theorem hopFramesCap_push (input cap : List HopFramesSymbol) :
    steinerUnaryHopSharedCapRowFramesMachine.step (hopFramesCfg (some .readCap) (hopFramesTally::input) cap [] []) =
      some (hopFramesCfg (some .readCap) input (hopFramesTally::cap) [] []) := by
  simp only [FinTM2.step,steinerUnaryHopSharedCapRowFramesMachine,hopFramesCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopFramesProgram,hopFramesRead,hopFramesSeen,hopFramesNext,hopFramesUpdate0,hopFramesUpdate1]
  rfl

private theorem hopFramesCap_end (input cap : List HopFramesSymbol) :
    steinerUnaryHopSharedCapRowFramesMachine.step (hopFramesCfg (some .readCap) (hopFramesCellMark::input) cap [] []) =
      some (hopFramesCfg (some .row) input cap [] []) := by
  simp only [FinTM2.step,steinerUnaryHopSharedCapRowFramesMachine,hopFramesCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopFramesProgram,hopFramesRead,hopFramesSeen,hopFramesNext,hopFramesUpdate0]
  rfl

private def hopFramesLoadCap (count : ℕ) (input cap : List HopFramesSymbol) :
    HopFramesRun (hopFramesCfg (some .readCap) (List.replicate count hopFramesTally++hopFramesCellMark::input) cap [] [])
      (hopFramesCfg (some .row) input (List.replicate count hopFramesTally++cap) [] []) (count+1) := by
  induction count generalizing cap with
  | zero => exact hopFramesOne (hopFramesCap_end _ _)
  | succ count ih =>
    have run := hopFramesThen (hopFramesOne (hopFramesCap_push _ cap)) (ih (hopFramesTally::cap))
    have saved : List.replicate count hopFramesTally++hopFramesTally::cap = List.replicate (count+1) hopFramesTally++cap := by
      rw [List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [saved] at run
    exact hopFramesRelax run (by omega)

private theorem hopFramesCopy_push (header : Bool) (symbol : HopFramesSymbol) (input cap work output : List HopFramesSymbol) :
    steinerUnaryHopSharedCapRowFramesMachine.step
      (hopFramesCfg (some (.copyCap header)) input (symbol::cap) work output) =
      some (hopFramesCfg (some (.copyCap header)) input cap (symbol::work) (symbol::output)) := by
  simp only [FinTM2.step,steinerUnaryHopSharedCapRowFramesMachine,hopFramesCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopFramesProgram,hopFramesRead,hopFramesSeen,hopFramesNext,hopFramesUpdate1,hopFramesUpdate2,hopFramesUpdate3]
  rfl

private theorem hopFramesCopy_end (header : Bool) (input work output : List HopFramesSymbol) :
    steinerUnaryHopSharedCapRowFramesMachine.step (hopFramesCfg (some (.copyCap header)) input [] work output) =
      some (hopFramesCfg (some (.restoreCap header)) input [] work (hopFramesField::output)) := by
  simp only [FinTM2.step,steinerUnaryHopSharedCapRowFramesMachine,hopFramesCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopFramesProgram,hopFramesRead,hopFramesSeen,hopFramesNext,hopFramesUpdate1,hopFramesUpdate3]
  rfl

private def hopFramesCopyCap (header : Bool) (input cap work output : List HopFramesSymbol) :
    HopFramesRun (hopFramesCfg (some (.copyCap header)) input cap work output)
      (hopFramesCfg (some (.restoreCap header)) input [] (cap.reverse++work)
        (hopFramesField::(cap.reverse++output))) (cap.length+1) := by
  induction cap generalizing work output with
  | nil => exact hopFramesOne (hopFramesCopy_end _ _ _ _)
  | cons symbol cap ih =>
    have run := hopFramesThen (hopFramesOne (hopFramesCopy_push header symbol input cap work output))
      (ih (symbol::work) (symbol::output))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,Nat.add_assoc,
      Nat.add_left_comm] using run

private theorem hopFramesRestore_push (header : Bool) (symbol : HopFramesSymbol) (input cap work output : List HopFramesSymbol) :
    steinerUnaryHopSharedCapRowFramesMachine.step
      (hopFramesCfg (some (.restoreCap header)) input cap (symbol::work) output) =
      some (hopFramesCfg (some (.restoreCap header)) input (symbol::cap) work output) := by
  simp only [FinTM2.step,steinerUnaryHopSharedCapRowFramesMachine,hopFramesCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopFramesProgram,hopFramesRead,hopFramesSeen,hopFramesNext,hopFramesUpdate1,hopFramesUpdate2]
  rfl

private theorem hopFramesRestore_end (header : Bool) (input cap output : List HopFramesSymbol) :
    steinerUnaryHopSharedCapRowFramesMachine.step (hopFramesCfg (some (.restoreCap header)) input cap [] output) =
      some (hopFramesCfg (some (hopFramesAfterCap header)) input cap [] output) := by
  simp only [FinTM2.step,steinerUnaryHopSharedCapRowFramesMachine,hopFramesCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopFramesProgram,hopFramesRead,hopFramesSeen,hopFramesNext,hopFramesUpdate2]
  rfl

private def hopFramesRestoreCap (header : Bool) (input cap work output : List HopFramesSymbol) :
    HopFramesRun (hopFramesCfg (some (.restoreCap header)) input cap work output)
      (hopFramesCfg (some (hopFramesAfterCap header)) input (work.reverse++cap) [] output) (work.length+1) := by
  induction work generalizing cap with
  | nil => exact hopFramesOne (hopFramesRestore_end _ _ _ _)
  | cons symbol work ih =>
    have run := hopFramesThen (hopFramesOne (hopFramesRestore_push header symbol input cap work output)) (ih (symbol::cap))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,Nat.add_assoc,
      Nat.add_left_comm] using run

private def hopFramesEmitCap (header : Bool) (input : List HopFramesSymbol) (cap : ℕ) (output : List HopFramesSymbol) :
    let stash := List.replicate cap hopFramesTally
    HopFramesRun (hopFramesCfg (some (.copyCap header)) input stash [] output)
      (hopFramesCfg (some (hopFramesAfterCap header)) input stash [] (hopFramesField::(stash++output))) (2*cap+2) := by
  let stash := List.replicate cap hopFramesTally
  have copy := hopFramesCopyCap header input stash [] output
  simp only [stash,List.reverse_replicate,List.append_nil,List.length_replicate] at copy
  have restore := hopFramesRestoreCap header input [] stash (hopFramesField::(stash++output))
  simp only [stash,List.reverse_replicate,List.append_nil,List.length_replicate] at restore
  exact hopFramesRelax (hopFramesThen copy restore) (by omega)

private theorem hopFramesRow_start (input cap output : List HopFramesSymbol) (nonempty : input ≠ []) :
    steinerUnaryHopSharedCapRowFramesMachine.step (hopFramesCfg (some .row) input cap [] output) =
      some (hopFramesCfg (some (.copyCap true)) input cap [] output) := by
  cases input with
  | nil => exact (nonempty rfl).elim
  | cons symbol input => rfl

private theorem hopFramesRow_eof (cap output : List HopFramesSymbol) :
    steinerUnaryHopSharedCapRowFramesMachine.step (hopFramesCfg (some .row) [] cap [] output) =
      some (hopFramesCfg (some .clear) [] cap [] output) := rfl

private theorem hopFramesCell_start (input cap output : List HopFramesSymbol)
    (notRow : input.head? ≠ some hopFramesRowMark) :
    steinerUnaryHopSharedCapRowFramesMachine.step (hopFramesCfg (some .cell) input cap [] output) =
      some (hopFramesCfg (some (.copyCap false)) input cap [] output) := by
  have different : (input.head? == some hopFramesRowMark) = false := by
    rcases input with _ | ⟨a | a, tail⟩
    · rfl
    · cases a
      · rfl
      · exact (notRow rfl).elim
    · rfl
  change some (bif input.head? == some hopFramesRowMark then
    Turing.TM2.stepAux (hopFramesRead 0 (push 3 hopFramesSeen (hopFramesNext .row))) input.head?
      (hopFramesTapes input cap [] output)
    else hopFramesCfg (some (.copyCap false)) input cap [] output) = _
  rw [different]
  rfl

private theorem hopFramesCell_rowEnd (input cap output : List HopFramesSymbol) :
    steinerUnaryHopSharedCapRowFramesMachine.step (hopFramesCfg (some .cell) (hopFramesRowMark::input) cap [] output) =
      some (hopFramesCfg (some .row) input cap [] (hopFramesRowMark::output)) := by
  simp only [FinTM2.step,steinerUnaryHopSharedCapRowFramesMachine,hopFramesCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopFramesProgram,hopFramesPeek,hopFramesRead,hopFramesSeen,hopFramesNext,hopFramesUpdate0,hopFramesUpdate3]
  rfl

private theorem hopFramesPayload_push (symbol : HopFramesSymbol) (payload cap output : List HopFramesSymbol)
    (legal : symbol ≠ hopFramesCellMark) :
    steinerUnaryHopSharedCapRowFramesMachine.step (hopFramesCfg (some .copyCell) (symbol::payload) cap [] output) =
      some (hopFramesCfg (some .copyCell) payload cap [] (symbol::output)) := by
  have check : ((some symbol : Option HopFramesSymbol) == some hopFramesCellMark) = false := by
    rcases symbol with b | b
    · cases b
      · exact (legal rfl).elim
      · rfl
    · rfl
  simp only [FinTM2.step,steinerUnaryHopSharedCapRowFramesMachine,hopFramesCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopFramesProgram,hopFramesRead,hopFramesSeen,hopFramesNext,hopFramesUpdate0,hopFramesUpdate3]
  change some (bif some symbol == some hopFramesCellMark then
    hopFramesCfg (some .cell) payload cap [] (symbol::hopFramesField::output) else
    hopFramesCfg (some .copyCell) payload cap [] (symbol::output)) = _
  rw [check]
  rfl

private theorem hopFramesPayload_end (input cap output : List HopFramesSymbol) :
    steinerUnaryHopSharedCapRowFramesMachine.step (hopFramesCfg (some .copyCell) (hopFramesCellMark::input) cap [] output) =
      some (hopFramesCfg (some .cell) input cap [] (hopFramesCellMark::hopFramesField::output)) := by
  simp only [FinTM2.step,steinerUnaryHopSharedCapRowFramesMachine,hopFramesCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopFramesProgram,hopFramesRead,hopFramesSeen,hopFramesNext,hopFramesUpdate0,hopFramesUpdate3]
  rfl

private def hopFramesPayloadCopy (payload input cap output : List HopFramesSymbol) (legal : hopFramesCellMark ∉ payload) :
    HopFramesRun (hopFramesCfg (some .copyCell) (payload++hopFramesCellMark::input) cap [] output)
      (hopFramesCfg (some .cell) input cap [] (hopFramesCellMark::hopFramesField::(payload.reverse++output)))
      (payload.length+1) := by
  induction payload generalizing output with
  | nil => exact hopFramesOne (hopFramesPayload_end _ _ _)
  | cons symbol payload ih =>
    simp only [List.mem_cons,not_or] at legal
    have run := hopFramesThen (hopFramesOne (hopFramesPayload_push symbol _ _ _ (Ne.symm legal.1)))
      (ih (symbol::output) legal.2)
    simpa only [List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,List.nil_append,List.length_cons,
      Nat.add_assoc,Nat.add_left_comm] using run

private def hopFramesRawPayload (cell : ℕ × ℕ) : List HopFramesSymbol :=
  List.replicate cell.1 hopFramesTally++hopFramesField::List.replicate cell.2 hopFramesTally

private def hopFramesRawCell (cell : ℕ × ℕ) : List HopFramesSymbol := hopFramesRawPayload cell++[hopFramesCellMark]

private def hopFramesRawCells (row : List (ℕ × ℕ)) : List HopFramesSymbol := row.flatMap hopFramesRawCell

private def hopFramesRawRows (rows : List (List (ℕ × ℕ))) : List HopFramesSymbol :=
  rows.flatMap fun row => hopFramesRawCells row++[hopFramesRowMark]

private def hopFramesHeader (cap : ℕ) : List HopFramesSymbol := List.replicate cap hopFramesTally++[hopFramesField]

private def hopFramesExpandedCell (cap : ℕ) (cell : ℕ × ℕ) : List HopFramesSymbol :=
  hopFramesHeader cap++hopFramesRawPayload cell++[hopFramesField,hopFramesCellMark]

private def hopFramesExpandedCells (cap : ℕ) (row : List (ℕ × ℕ)) : List HopFramesSymbol :=
  row.flatMap (hopFramesExpandedCell cap)

private def hopFramesExpandedRow (cap : ℕ) (row : List (ℕ × ℕ)) : List HopFramesSymbol :=
  hopFramesHeader cap++hopFramesExpandedCells cap row++[hopFramesRowMark]

private def hopFramesExpandedRows (cap : ℕ) (rows : List (List (ℕ × ℕ))) : List HopFramesSymbol :=
  rows.flatMap (hopFramesExpandedRow cap)

private theorem hopFramesRawCell_cons (cell : ℕ × ℕ) (row : List (ℕ × ℕ)) :
    hopFramesRawCells (cell::row) = hopFramesRawPayload cell++hopFramesCellMark::hopFramesRawCells row := by
  simp only [hopFramesRawCells,hopFramesRawCell,List.flatMap_cons,List.append_assoc,List.singleton_append]

private theorem hopFramesRawRows_cons (row : List (ℕ × ℕ)) (rows : List (List (ℕ × ℕ))) :
    hopFramesRawRows (row::rows) = hopFramesRawCells row++hopFramesRowMark::hopFramesRawRows rows := by
  simp only [hopFramesRawRows,List.flatMap_cons,List.append_assoc,List.singleton_append]

private theorem hopFramesPayload_legal (cell : ℕ × ℕ) : hopFramesCellMark ∉ hopFramesRawPayload cell := by
  simp [hopFramesRawPayload,hopFramesCellMark,hopFramesTally,hopFramesField,List.mem_replicate]

private theorem hopFramesCell_word_start (cell : ℕ × ℕ) (tail : List HopFramesSymbol) :
    (hopFramesRawPayload cell++hopFramesCellMark::tail).head? ≠ some hopFramesRowMark := by
  have missing : hopFramesRowMark ∉ hopFramesRawPayload cell := by
    simp [hopFramesRawPayload,hopFramesRowMark,hopFramesTally,hopFramesField,List.mem_replicate]
  cases word : hopFramesRawPayload cell with
  | nil => simp [hopFramesRowMark,hopFramesCellMark]
  | cons symbol rest =>
    intro equal
    have head : symbol = hopFramesRowMark := Option.some.inj (by
      simpa only [word,List.cons_append,List.head?_cons] using equal)
    apply missing
    simp [word,head]

private def hopFramesOneCell (cap : ℕ) (cell : ℕ × ℕ) (input output : List HopFramesSymbol) :
    let stash := List.replicate cap hopFramesTally
    let raw := hopFramesRawPayload cell
    HopFramesRun (hopFramesCfg (some .cell) (raw++hopFramesCellMark::input) stash [] output)
      (hopFramesCfg (some .cell) input stash [] ((hopFramesExpandedCell cap cell).reverse++output))
      ((2*cap+4)*(raw.length+1)) := by
  let stash := List.replicate cap hopFramesTally
  let raw := hopFramesRawPayload cell
  let word := raw++hopFramesCellMark::input
  have start := hopFramesOne (hopFramesCell_start word stash output (hopFramesCell_word_start cell input))
  have header := hopFramesEmitCap false word cap output
  have payload := hopFramesPayloadCopy raw input stash (hopFramesField::(stash++output)) (hopFramesPayload_legal cell)
  have shaped : hopFramesCellMark::hopFramesField::(raw.reverse++hopFramesField::(stash++output)) =
      (hopFramesExpandedCell cap cell).reverse++output := by
    simp only [hopFramesExpandedCell,hopFramesHeader,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
      List.reverse_replicate,List.append_assoc,List.cons_append,raw,stash]
  rw [shaped] at payload
  have run := hopFramesThen (hopFramesThen start header) payload
  refine hopFramesRelax run ?_
  change 1+(2*cap+2)+(raw.length+1) ≤ (2*cap+4)*(raw.length+1)
  have paid := Nat.mul_le_mul_right raw.length (show 1 ≤ 2*cap+4 by omega)
  simp only [Nat.mul_add,Nat.mul_one,Nat.one_mul] at paid ⊢
  omega

private def hopFramesAllCells (cap : ℕ) (row : List (ℕ × ℕ)) (input output : List HopFramesSymbol) :
    let stash := List.replicate cap hopFramesTally
    let raw := hopFramesRawCells row
    HopFramesRun (hopFramesCfg (some .cell) (raw++hopFramesRowMark::input) stash [] output)
      (hopFramesCfg (some .row) input stash [] (hopFramesRowMark::((hopFramesExpandedCells cap row).reverse++output)))
      ((2*cap+4)*raw.length+1) := by
  induction row generalizing output with
  | nil => exact hopFramesOne (hopFramesCell_rowEnd _ _ _)
  | cons cell row ih =>
    dsimp only
    rw [hopFramesRawCell_cons]
    have first := hopFramesOneCell cap cell (hopFramesRawCells row++hopFramesRowMark::input) output
    have rest := ih ((hopFramesExpandedCell cap cell).reverse++output)
    have run := hopFramesThen first rest
    simp only [hopFramesExpandedCells,List.flatMap_cons,List.reverse_append,List.append_assoc,List.length_append,
      List.length_cons]
    refine hopFramesRelax run ?_
    simp only [Nat.mul_add,Nat.mul_one]
    omega

private def hopFramesOneRow (cap : ℕ) (row : List (ℕ × ℕ)) (input output : List HopFramesSymbol) :
    let stash := List.replicate cap hopFramesTally
    let raw := hopFramesRawCells row
    let expanded := hopFramesExpandedRow cap row
    HopFramesRun (hopFramesCfg (some .row) (raw++hopFramesRowMark::input) stash [] output)
      (hopFramesCfg (some .row) input stash [] (expanded.reverse++output)) ((2*cap+4)*(raw.length+1)) := by
  let stash := List.replicate cap hopFramesTally
  let raw := hopFramesRawCells row
  let word := raw++hopFramesRowMark::input
  have start := hopFramesOne (hopFramesRow_start word stash output (by simp [word]))
  have header := hopFramesEmitCap true word cap output
  have cells := hopFramesAllCells cap row input (hopFramesField::(stash++output))
  have run := hopFramesThen (hopFramesThen start header) cells
  have shaped : hopFramesRowMark::((hopFramesExpandedCells cap row).reverse++hopFramesField::(stash++output)) =
      (hopFramesExpandedRow cap row).reverse++output := by
    simp only [hopFramesExpandedRow,hopFramesHeader,List.reverse_append,List.reverse_replicate,List.reverse_cons,
      List.reverse_nil,List.nil_append,List.append_assoc,List.cons_append,stash]
  rw [shaped] at run
  refine hopFramesRelax run ?_
  change _ ≤ (2*cap+4)*(raw.length+1)
  simp only [Nat.mul_add,Nat.mul_one,raw]
  omega

private def hopFramesAllRows (cap : ℕ) (rows : List (List (ℕ × ℕ))) (output : List HopFramesSymbol) :
    let stash := List.replicate cap hopFramesTally
    let raw := hopFramesRawRows rows
    HopFramesRun (hopFramesCfg (some .row) raw stash [] output)
      (hopFramesCfg (some .clear) [] stash [] ((hopFramesExpandedRows cap rows).reverse++output))
      ((2*cap+4)*raw.length+1) := by
  induction rows generalizing output with
  | nil => exact hopFramesOne (hopFramesRow_eof _ _)
  | cons row rows ih =>
    dsimp only
    rw [hopFramesRawRows_cons]
    let expanded := hopFramesExpandedRow cap row
    have first := hopFramesOneRow cap row (hopFramesRawRows rows) output
    have rest := ih (expanded.reverse++output)
    have run := hopFramesThen first rest
    simp only [hopFramesExpandedRows,List.flatMap_cons,List.reverse_append,List.append_assoc,List.length_append,
      List.length_cons]
    refine hopFramesRelax run ?_
    simp only [Nat.mul_add,Nat.mul_one]
    omega

private theorem hopFramesClear_push (symbol : HopFramesSymbol) (cap output : List HopFramesSymbol) :
    steinerUnaryHopSharedCapRowFramesMachine.step (hopFramesCfg (some .clear) [] (symbol::cap) [] output) =
      some (hopFramesCfg (some .clear) [] cap [] output) := by
  simp only [FinTM2.step,steinerUnaryHopSharedCapRowFramesMachine,hopFramesCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopFramesProgram,hopFramesRead,hopFramesNext,hopFramesUpdate1]
  rfl

private theorem hopFramesClear_end (output : List HopFramesSymbol) :
    steinerUnaryHopSharedCapRowFramesMachine.step (hopFramesCfg (some .clear) [] [] [] output) =
      some (hopFramesCfg (some .finish) [] [] [] output) := by
  simp only [FinTM2.step,steinerUnaryHopSharedCapRowFramesMachine,hopFramesCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopFramesProgram,hopFramesRead,hopFramesNext,hopFramesUpdate1]
  rfl

private def hopFramesClear (cap output : List HopFramesSymbol) :
    HopFramesRun (hopFramesCfg (some .clear) [] cap [] output)
      (hopFramesCfg (some .finish) [] [] [] output) (cap.length+1) := by
  induction cap with
  | nil => exact hopFramesOne (hopFramesClear_end _)
  | cons symbol cap ih =>
    have run := hopFramesThen (hopFramesOne (hopFramesClear_push symbol cap output)) ih
    exact hopFramesRelax run (by simp only [List.length_cons]; omega)

private theorem hopFramesFinish_push (symbol : HopFramesSymbol) (input output : List HopFramesSymbol) :
    steinerUnaryHopSharedCapRowFramesMachine.step (hopFramesCfg (some .finish) input [] [] (symbol::output)) =
      some (hopFramesCfg (some .finish) (symbol::input) [] [] output) := by
  simp only [FinTM2.step,steinerUnaryHopSharedCapRowFramesMachine,hopFramesCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopFramesProgram,hopFramesRead,hopFramesSeen,hopFramesNext,hopFramesUpdate0,hopFramesUpdate3]
  rfl

private theorem hopFramesFinish_end (input : List HopFramesSymbol) :
    steinerUnaryHopSharedCapRowFramesMachine.step (hopFramesCfg (some .finish) input [] [] []) =
      some (hopFramesCfg none input [] [] []) := by
  simp only [FinTM2.step,steinerUnaryHopSharedCapRowFramesMachine,hopFramesCfg,Turing.TM2.step,Turing.TM2.stepAux,
    hopFramesProgram,hopFramesRead,hopFramesSeen,hopFramesNext,hopFramesUpdate3]
  rfl

private def hopFramesFinish (input output : List HopFramesSymbol) :
    HopFramesRun (hopFramesCfg (some .finish) input [] [] output)
      (hopFramesCfg none (output.reverse++input) [] [] []) (output.length+1) := by
  induction output generalizing input with
  | nil => exact hopFramesOne (hopFramesFinish_end _)
  | cons symbol output ih =>
    have run := hopFramesThen (hopFramesOne (hopFramesFinish_push symbol input output)) (ih (symbol::input))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,Nat.add_left_comm,List.length_cons]
      using run

private theorem hopFramesInput_eq (cap : ℕ) (rows : List (List (ℕ × ℕ))) :
    encodeSteinerUnarySharedCapRows (cap,rows) =
      List.replicate cap hopFramesTally++hopFramesCellMark::hopFramesRawRows rows := by
  let encodedCell : ℕ × ℕ → List HopFramesSymbol := fun cell =>
    ((List.replicate cell.1 (some true)++none::List.replicate cell.2 (some true)).map Sum.inr)++[hopFramesCellMark]
  have cells : encodedCell = hopFramesRawCell := by
    funext cell
    simp only [encodedCell,List.map_append,List.map_cons,List.map_replicate,hopFramesRawCell,hopFramesRawPayload,
      hopFramesTally,hopFramesField]
  change List.replicate cap hopFramesTally++hopFramesCellMark::(rows.flatMap fun row =>
    row.flatMap encodedCell++[hopFramesRowMark]) = _
  rw [cells]
  rfl

private theorem hopFramesExpandedCell_eq (cap : ℕ) (cell : ℕ × ℕ) :
    hopFramesExpandedCell cap cell = encodeSteinerUnaryHopTransferCandidate (cap,cell.1,cell.2)++[hopFramesCellMark] := by
  simp only [hopFramesExpandedCell,hopFramesHeader,hopFramesRawPayload,hopFramesTally,hopFramesField,
    encodeSteinerUnaryHopTransferCandidate,encodeSteinerUnaryRoundPriorVector,List.flatMap_cons,List.flatMap_nil,
    List.append_assoc,List.cons_append,List.append_nil,List.nil_append]

private theorem hopFramesExpandedRow_eq (cap : ℕ) (row : List (ℕ × ℕ)) :
    hopFramesExpandedRow cap row = encodeSteinerUnaryHopMinimumRowFrame (cap,row)++[hopFramesRowMark] := by
  have header : hopFramesHeader cap = encodeSteinerUnaryRoundPriorVector [cap] := by
    simp only [hopFramesHeader,hopFramesTally,hopFramesField,encodeSteinerUnaryRoundPriorVector,List.flatMap_cons,
      List.flatMap_nil,List.append_nil]
  change hopFramesHeader cap++row.flatMap (hopFramesExpandedCell cap)++[hopFramesRowMark] =
    (encodeSteinerUnaryRoundPriorVector [cap]++row.flatMap (fun cell =>
      encodeSteinerUnaryHopTransferCandidate (cap,cell.1,cell.2)++[hopFramesCellMark]))++[hopFramesRowMark]
  rw [header,show hopFramesExpandedCell cap = _ from funext (hopFramesExpandedCell_eq cap),List.append_assoc]

/-- Expand each row, including an empty row, and retain its row marker. -/
def steinerUnaryHopSharedCapRowFramesAnswer (request : SteinerUnarySharedCapRows) : List SteinerUnaryCappedRowsSymbol :=
  request.2.flatMap fun row => encodeSteinerUnaryHopMinimumRowFrame (request.1,row)++[hopFramesRowMark]

private theorem hopFramesAnswer_eq (cap : ℕ) (rows : List (List (ℕ × ℕ))) :
    hopFramesExpandedRows cap rows = steinerUnaryHopSharedCapRowFramesAnswer (cap,rows) := by
  unfold hopFramesExpandedRows steinerUnaryHopSharedCapRowFramesAnswer
  apply congrArg (List.flatMap · rows)
  exact funext (hopFramesExpandedRow_eq cap)

private theorem hopFramesCellSize (cap : ℕ) (cell : ℕ × ℕ) :
    (hopFramesExpandedCell cap cell).length ≤ (cap+3)*(hopFramesRawCell cell).length := by
  simp only [hopFramesExpandedCell,hopFramesHeader,hopFramesRawCell,List.length_append,List.length_replicate,
    List.length_cons,List.length_nil,Nat.mul_add,Nat.mul_one]
  have charged := Nat.mul_le_mul_right (hopFramesRawPayload cell).length (show 1 ≤ cap+3 by omega)
  rw [Nat.one_mul] at charged
  omega

private theorem hopFramesCellsSize (cap : ℕ) (row : List (ℕ × ℕ)) :
    (hopFramesExpandedCells cap row).length ≤ (cap+3)*(hopFramesRawCells row).length := by
  induction row with
  | nil => exact le_rfl
  | cons cell row ih =>
    simp only [hopFramesExpandedCells,hopFramesRawCells,List.flatMap_cons,List.length_append,Nat.mul_add]
    exact Nat.add_le_add (hopFramesCellSize cap cell) ih

private theorem hopFramesRowSize (cap : ℕ) (row : List (ℕ × ℕ)) :
    (hopFramesExpandedRow cap row).length ≤ (cap+3)*((hopFramesRawCells row).length+1) := by
  have cells := hopFramesCellsSize cap row
  simp only [hopFramesExpandedRow,hopFramesHeader,List.length_append,List.length_replicate,List.length_cons,
    List.length_nil,Nat.mul_add,Nat.mul_one]
  omega

private theorem hopFramesRowsSize (cap : ℕ) (rows : List (List (ℕ × ℕ))) :
    (hopFramesExpandedRows cap rows).length ≤ (cap+3)*(hopFramesRawRows rows).length := by
  induction rows with
  | nil => exact le_rfl
  | cons row rows ih =>
    change (hopFramesExpandedRow cap row++hopFramesExpandedRows cap rows).length ≤
      (cap+3)*((hopFramesRawCells row++[hopFramesRowMark])++hopFramesRawRows rows).length
    simp only [List.length_append,List.length_cons,List.length_nil,Nat.mul_add,Nat.mul_one]
    have first := hopFramesRowSize cap row
    simp only [Nat.mul_add,Nat.mul_one] at first
    omega

/-- At most a factor cap+3 is needed to store the expanded rows. -/
theorem steinerUnaryHopSharedCapRowFramesAnswer_length_le (request : SteinerUnarySharedCapRows) :
    (steinerUnaryHopSharedCapRowFramesAnswer request).length ≤
      (request.1+3)*(encodeSteinerUnarySharedCapRows request).length := by
  rcases request with ⟨cap,rows⟩
  rw [← hopFramesAnswer_eq,hopFramesInput_eq]
  have fits : (hopFramesRawRows rows).length ≤
      (List.replicate cap hopFramesTally++hopFramesCellMark::hopFramesRawRows rows).length := by
    simp only [List.length_append,List.length_cons,List.length_replicate]
    omega
  exact (hopFramesRowsSize cap rows).trans (Nat.mul_le_mul_left _ fits)

private theorem hopFrames_init (word : List HopFramesSymbol) :
    initList steinerUnaryHopSharedCapRowFramesMachine word = hopFramesCfg (some .readCap) word [] [] [] := by
  apply congrArg (fun tapes : Fin 4 → List HopFramesSymbol =>
    (⟨some .readCap,none,tapes⟩ : steinerUnaryHopSharedCapRowFramesMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem hopFrames_halt (word : List HopFramesSymbol) :
    haltList steinerUnaryHopSharedCapRowFramesMachine word = hopFramesCfg none word [] [] [] := by
  apply congrArg (fun tapes : Fin 4 → List HopFramesSymbol =>
    (⟨none,none,tapes⟩ : steinerUnaryHopSharedCapRowFramesMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- One shared sentinel supplies the row headers and cell frames in
quadratic native time in the compact pair frame. -/
def steinerUnaryHopSharedCapRowFramesMachine_run (request : SteinerUnarySharedCapRows) :
    let input := encodeSteinerUnarySharedCapRows request
    TM2OutputsInTime steinerUnaryHopSharedCapRowFramesMachine input
      (some (steinerUnaryHopSharedCapRowFramesAnswer request)) (3*input.length^2+9*input.length+4) := by
  rcases request with ⟨cap,rows⟩
  let input := encodeSteinerUnarySharedCapRows (cap,rows)
  let raw := hopFramesRawRows rows
  let expanded := hopFramesExpandedRows cap rows
  let stash := List.replicate cap hopFramesTally
  let X := input.length
  have loaded := hopFramesLoadCap cap raw []
  rw [List.append_nil] at loaded
  have allRows := hopFramesAllRows cap rows []
  simp only [List.append_nil] at allRows
  have clear := hopFramesClear stash expanded.reverse
  simp only [stash,List.length_replicate] at clear
  have finish := hopFramesFinish [] expanded.reverse
  rw [List.reverse_reverse,List.append_nil,List.length_reverse] at finish
  have run := hopFramesThen (hopFramesThen (hopFramesThen loaded allRows) clear) finish
  change HopFramesRun (initList steinerUnaryHopSharedCapRowFramesMachine input) (haltList steinerUnaryHopSharedCapRowFramesMachine _) _
  have inputEq : input = List.replicate cap hopFramesTally++hopFramesCellMark::raw := hopFramesInput_eq cap rows
  rw [hopFrames_init,hopFrames_halt,← hopFramesAnswer_eq]
  rw [← inputEq] at run
  refine hopFramesRelax run ?_
  have length : X = cap+raw.length+1 := by
    dsimp only [X,input,raw]
    rw [hopFramesInput_eq]
    simp only [List.length_append,List.length_cons,List.length_replicate]
    omega
  have expandSize : expanded.length ≤ (cap+3)*raw.length := hopFramesRowsSize cap rows
  have arithmetic : (2*cap+4)*raw.length+(cap+3)*raw.length = (3*cap+7)*raw.length := by ring
  have fit := Nat.mul_le_mul (show 3*cap+7 ≤ 3*X+7 by omega) (show raw.length ≤ X by omega)
  have ending : (3*X+7)*X+2*X+4 = 3*X^2+9*X+4 := by ring
  change (cap+1)+((2*cap+4)*raw.length+1)+(cap+1)+(expanded.length+1) ≤ 3*X^2+9*X+4
  omega

/-- The expanded row adapter has an actual quadratic transition polynomial. -/
noncomputable def steinerUnaryHopSharedCapRowFramesMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnarySharedCapRows id steinerUnaryHopSharedCapRowFramesAnswer where
  tm := steinerUnaryHopSharedCapRowFramesMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 3*Polynomial.X^2+Polynomial.C 9*Polynomial.X+Polynomial.C 4
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_C,
      Polynomial.eval_pow,Polynomial.eval_X] using steinerUnaryHopSharedCapRowFramesMachine_run request

end OnlineReachabilityPreservers
