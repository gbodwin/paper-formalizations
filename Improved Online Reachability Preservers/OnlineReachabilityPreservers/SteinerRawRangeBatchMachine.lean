import OnlineReachabilityPreservers.SteinerBinaryRangeMachine
import OnlineReachabilityPreservers.SteinerStackFrame
import OnlineReachabilityPreservers.SteinerStackReturn

/-! A finite stack machine for consecutive raw-word endpoint comparisons. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

/-- An outer divider separates successive comparison requests. A tagged
inner divider separates the two binary words of one request. -/
abbrev SteinerRawRangeSymbol := Option (Option Bool)

private inductive RawRangeLabel where
  | collect (accepted : Bool)
  | restore (accepted : Bool)
  | compare (accepted : Bool) (label : Fin 3)
  | record (accepted : Bool)
  deriving Fintype

private abbrev RawRangeCompareRegister := steinerBinaryComparisonMachine.σ
private abbrev RawRangeRegister := Option SteinerRawRangeSymbol × RawRangeCompareRegister
private abbrev RawRangeProgram :=
  Turing.TM2.Stmt (fun _ : Fin 4 => SteinerRawRangeSymbol) RawRangeLabel RawRangeRegister

private def rawRangeInitial : RawRangeRegister := (none,steinerBinaryComparisonMachine.initialState)

private def rawRangeObserve (_ : RawRangeRegister) (seen : Option SteinerRawRangeSymbol) : RawRangeRegister :=
  (seen,steinerBinaryComparisonMachine.initialState)

private def rawRangeCompareSlots : Fin 3 ↪ Fin 4 :=
  ⟨Fin.castSucc,Fin.castSucc_injective _⟩

private def rawRangeCompareTag (accepted : Bool) :
    StackMachineTag (Option Bool) SteinerRawRangeSymbol (Fin 3) RawRangeLabel
      RawRangeCompareRegister RawRangeRegister where
  writeSymbol := some
  readSymbol := id
  writeRegister r := (none,r)
  readRegister := Prod.snd
  writeLabel := RawRangeLabel.compare accepted
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def rawRangeTaggedCompareProgram :
    RawRangeLabel → StackMachineTag.Program (Fin 3) SteinerRawRangeSymbol RawRangeLabel RawRangeRegister
  | .compare accepted label =>
    (rawRangeCompareTag accepted).returningStatement (.record accepted) (steinerBinaryComparisonMachine.m label)
  | _ => halt

private def rawRangeProgram : RawRangeLabel → RawRangeProgram
  | .collect accepted =>
    pop 3 rawRangeObserve <|
      branch (fun r => r.1.isSome)
        (branch (fun r => r.1.join.isSome)
          (push 1 (fun r => r.1.getD none) <| load (fun _ => rawRangeInitial) <| goto (fun _ => .collect accepted))
          (load (fun _ => rawRangeInitial) <| goto (fun _ => .restore accepted)))
        (push 3 (fun _ => some (some accepted)) <| load (fun _ => rawRangeInitial) halt)
  | .restore accepted =>
    pop 1 rawRangeObserve <|
      branch (fun r => r.1.isSome)
        (push 0 (fun r => r.1.getD none) <| load (fun _ => rawRangeInitial) <| goto (fun _ => .restore accepted))
        (load (fun _ => rawRangeInitial) <| goto (fun _ => .compare accepted 0))
  | .compare accepted label =>
    StackIndexEmbedding.statement rawRangeCompareSlots (rawRangeTaggedCompareProgram (.compare accepted label))
  | .record accepted =>
    pop 0 rawRangeObserve <| pop 0 (fun r _ => r) <|
      branch (fun r => accepted && r.1.join.join.getD false)
        (load (fun _ => rawRangeInitial) <| goto (fun _ => .collect true))
        (load (fun _ => rawRangeInitial) <| goto (fun _ => .collect false))

/-- Process each comparison in order, holding the later requests on
a passive tape while the verified comparison subroutine runs. -/
abbrev steinerRawRangeBatchMachine : FinTM2 where
  K := Fin 4
  k₀ := 3
  k₁ := 3
  Γ _ := SteinerRawRangeSymbol
  Λ := RawRangeLabel
  main := .collect true
  σ := RawRangeRegister
  initialState := rawRangeInitial
  m := rawRangeProgram

/-- Encode raw words with an inner divider and terminate each request
with an outer divider. The bit pairs need not be aligned in advance. -/
def encodeSteinerRawRangeBatch (checks : List SteinerRangeWordPair) : List SteinerRawRangeSymbol :=
  checks.flatMap fun check => (encodeSteinerBinaryComparison check).map some ++ [none]

def encodeSteinerRawRangeAnswer (accepted : Bool) : List SteinerRawRangeSymbol := [some (some accepted)]

private def rawRangeCfg (label : Option RawRangeLabel) (active buffer queued : List SteinerRawRangeSymbol) :
    steinerRawRangeBatchMachine.Cfg where
  l := label
  var := rawRangeInitial
  stk := ![active,buffer,[],queued]

private theorem rawRange_update0 (a b q next : List SteinerRawRangeSymbol) :
    Function.update (![a,b,[],q] : Fin 4 → List SteinerRawRangeSymbol) 0 next = ![next,b,[],q] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem rawRange_update1 (a b q next : List SteinerRawRangeSymbol) :
    Function.update (![a,b,[],q] : Fin 4 → List SteinerRawRangeSymbol) 1 next = ![a,next,[],q] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem rawRange_update3 (a b q next : List SteinerRawRangeSymbol) :
    Function.update (![a,b,[],q] : Fin 4 → List SteinerRawRangeSymbol) 3 next = ![a,b,[],next] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem rawRange_collectSymbol (accepted : Bool) (symbol : Option Bool)
    (buffer tail : List SteinerRawRangeSymbol) :
    steinerRawRangeBatchMachine.step (rawRangeCfg (some (.collect accepted)) [] buffer (some symbol::tail)) =
      some (rawRangeCfg (some (.collect accepted)) [] (some symbol::buffer) tail) := by
  simp [FinTM2.step,steinerRawRangeBatchMachine,rawRangeCfg,Turing.TM2.step,Turing.TM2.stepAux,
    rawRangeProgram,rawRangeObserve,rawRange_update1,rawRange_update3]
  rfl

private theorem rawRange_collectDone (accepted : Bool) (buffer tail : List SteinerRawRangeSymbol) :
    steinerRawRangeBatchMachine.step (rawRangeCfg (some (.collect accepted)) [] buffer (none::tail)) =
      some (rawRangeCfg (some (.restore accepted)) [] buffer tail) := by
  simp [FinTM2.step,steinerRawRangeBatchMachine,rawRangeCfg,Turing.TM2.step,Turing.TM2.stepAux,
    rawRangeProgram,rawRangeObserve,rawRange_update3]
  rfl

private theorem rawRange_batchDone (accepted : Bool) :
    steinerRawRangeBatchMachine.step (rawRangeCfg (some (.collect accepted)) [] [] []) =
      some (rawRangeCfg none [] [] (encodeSteinerRawRangeAnswer accepted)) := by
  simp [FinTM2.step,steinerRawRangeBatchMachine,rawRangeCfg,Turing.TM2.step,Turing.TM2.stepAux,
    rawRangeProgram,rawRangeObserve,rawRange_update3,encodeSteinerRawRangeAnswer]
  rfl

private theorem rawRange_restoreSymbol (accepted : Bool) (symbol : SteinerRawRangeSymbol)
    (active buffer tail : List SteinerRawRangeSymbol) :
    steinerRawRangeBatchMachine.step (rawRangeCfg (some (.restore accepted)) active (symbol::buffer) tail) =
      some (rawRangeCfg (some (.restore accepted)) (symbol::active) buffer tail) := by
  simp [FinTM2.step,steinerRawRangeBatchMachine,rawRangeCfg,Turing.TM2.step,Turing.TM2.stepAux,
    rawRangeProgram,rawRangeObserve,rawRange_update0,rawRange_update1]
  rfl

private theorem rawRange_restoreDone (accepted : Bool) (active tail : List SteinerRawRangeSymbol) :
    steinerRawRangeBatchMachine.step (rawRangeCfg (some (.restore accepted)) active [] tail) =
      some (rawRangeCfg (some (.compare accepted 0)) active [] tail) := by
  simp [FinTM2.step,steinerRawRangeBatchMachine,rawRangeCfg,Turing.TM2.step,Turing.TM2.stepAux,
    rawRangeProgram,rawRangeObserve,rawRange_update1]
  rfl

private theorem rawRange_record (accepted ordered same : Bool) (tail : List SteinerRawRangeSymbol) :
    steinerRawRangeBatchMachine.step
      (rawRangeCfg (some (.record accepted)) [some (some ordered),some (some same)] [] tail) =
      some (rawRangeCfg (some (.collect (accepted && ordered))) [] [] tail) := by
  cases accepted <;> cases ordered <;>
    simp [FinTM2.step,steinerRawRangeBatchMachine,rawRangeCfg,Turing.TM2.step,Turing.TM2.stepAux,
      rawRangeProgram,rawRangeObserve,rawRange_update0] <;> rfl

private def rawRangeOne {a b : steinerRawRangeBatchMachine.Cfg}
    (step : steinerRawRangeBatchMachine.step a = some b) :
    EvalsToInTime steinerRawRangeBatchMachine.step a (some b) 1 where
  steps := 1
  evals_in_steps := by change steinerRawRangeBatchMachine.step a = some b; exact step
  steps_le_m := le_rfl

private def rawRange_collectFrame (accepted : Bool) (symbols : List (Option Bool))
    (buffer tail : List SteinerRawRangeSymbol) :
    EvalsToInTime steinerRawRangeBatchMachine.step
      (rawRangeCfg (some (.collect accepted)) [] buffer (symbols.map some ++ none::tail))
      (some (rawRangeCfg (some (.restore accepted)) [] ((symbols.map some).reverse++buffer) tail))
      (symbols.length+1) := by
  induction symbols generalizing buffer with
  | nil => exact rawRangeOne (rawRange_collectDone accepted buffer tail)
  | cons symbol symbols ih =>
    have first := rawRangeOne (rawRange_collectSymbol accepted symbol buffer (symbols.map some ++ none::tail))
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (some symbol::buffer))
    simpa only [List.map_cons,List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,
      List.nil_append,List.length_cons] using all

private def rawRange_restoreFrame (accepted : Bool) (buffer active tail : List SteinerRawRangeSymbol) :
    EvalsToInTime steinerRawRangeBatchMachine.step (rawRangeCfg (some (.restore accepted)) active buffer tail)
      (some (rawRangeCfg (some (.compare accepted 0)) (buffer.reverse++active) [] tail)) (buffer.length+1) := by
  induction buffer generalizing active with
  | nil => exact rawRangeOne (rawRange_restoreDone accepted active tail)
  | cons symbol buffer ih =>
    have first := rawRangeOne (rawRange_restoreSymbol accepted symbol active buffer tail)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (symbol::active))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons] using all

private def rawRangePassive (tail : List SteinerRawRangeSymbol) (i : Fin 4) : List SteinerRawRangeSymbol :=
  if i = 3 then tail else []

private theorem rawRangeCompareSlots_excludes_last (i : Fin 3) : rawRangeCompareSlots i ≠ 3 := by
  fin_cases i <;> decide

private noncomputable def rawRangeTranslated (accepted : Bool) (tail : List SteinerRawRangeSymbol)
    (c : steinerBinaryComparisonMachine.Cfg) : steinerRawRangeBatchMachine.Cfg :=
  StackIndexEmbedding.configuration rawRangeCompareSlots (rawRangePassive tail)
    ((rawRangeCompareTag accepted).returningConfiguration (.record accepted) c)

private theorem rawRange_translateStep (accepted : Bool) (tail : List SteinerRawRangeSymbol)
    {c after : steinerBinaryComparisonMachine.Cfg} (step : steinerBinaryComparisonMachine.step c = some after) :
    steinerRawRangeBatchMachine.step (rawRangeTranslated accepted tail c) = some (rawRangeTranslated accepted tail after) := by
  let tag := rawRangeCompareTag accepted
  have tagged := tag.step_embedded_return (.record accepted) (base := steinerBinaryComparisonMachine.m)
    (host := rawRangeTaggedCompareProgram) (fun _ => rfl) step
  have framed := StackIndexEmbedding.step_on rawRangeCompareSlots (base := rawRangeTaggedCompareProgram)
    (rawRangePassive tail) (tag.returningConfiguration (.record accepted) c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem rawRange_compareInit (accepted : Bool) (tape : List (Option Bool)) (tail : List SteinerRawRangeSymbol) :
    rawRangeTranslated accepted tail (initList steinerBinaryComparisonMachine tape) =
      rawRangeCfg (some (.compare accepted 0)) (tape.map some) [] tail := by
  apply congrArg (fun stk : Fin 4 → List SteinerRawRangeSymbol =>
    (⟨some (RawRangeLabel.compare accepted 0),rawRangeInitial,stk⟩ : steinerRawRangeBatchMachine.Cfg))
  funext i
  fin_cases i
  · change StackIndexEmbedding.tapesAt rawRangeCompareSlots _ (rawRangePassive tail) (rawRangeCompareSlots 0) = _
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change StackIndexEmbedding.tapesAt rawRangeCompareSlots _ (rawRangePassive tail) (rawRangeCompareSlots 1) = _
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change StackIndexEmbedding.tapesAt rawRangeCompareSlots _ (rawRangePassive tail) (rawRangeCompareSlots 2) = _
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change StackIndexEmbedding.tapesAt rawRangeCompareSlots _ (rawRangePassive tail) 3 = tail
    rw [StackIndexEmbedding.tapesAt_extra _ _ _ rawRangeCompareSlots_excludes_last,rawRangePassive,ite_eq_left rfl]

private theorem rawRange_compareReturn (accepted : Bool) (out : List (Option Bool)) (tail : List SteinerRawRangeSymbol) :
    rawRangeTranslated accepted tail (haltList steinerBinaryComparisonMachine out) =
      rawRangeCfg (some (.record accepted)) (out.map some) [] tail := by
  apply congrArg (fun stk : Fin 4 → List SteinerRawRangeSymbol =>
    (⟨some (RawRangeLabel.record accepted),rawRangeInitial,stk⟩ : steinerRawRangeBatchMachine.Cfg))
  funext i
  fin_cases i
  · change StackIndexEmbedding.tapesAt rawRangeCompareSlots _ (rawRangePassive tail) (rawRangeCompareSlots 0) = _
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change StackIndexEmbedding.tapesAt rawRangeCompareSlots _ (rawRangePassive tail) (rawRangeCompareSlots 1) = _
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change StackIndexEmbedding.tapesAt rawRangeCompareSlots _ (rawRangePassive tail) (rawRangeCompareSlots 2) = _
    rw [StackIndexEmbedding.tapesAt_image]
    rfl
  · change StackIndexEmbedding.tapesAt rawRangeCompareSlots _ (rawRangePassive tail) 3 = tail
    rw [StackIndexEmbedding.tapesAt_extra _ _ _ rawRangeCompareSlots_excludes_last,rawRangePassive,ite_eq_left rfl]

private def rawRange_compareEval (accepted : Bool) (check : SteinerRangeWordPair) (tail : List SteinerRawRangeSymbol) :
    EvalsToInTime steinerRawRangeBatchMachine.step
      (rawRangeCfg (some (.compare accepted 0)) ((encodeSteinerBinaryComparison check).map some) [] tail)
      (some (rawRangeCfg (some (.record accepted)) ((steinerBinaryComparisonOutput check).map some) [] tail))
      (3*check.1.length+check.2.length+3) := by
  let run := steinerBinaryComparisonMachine_run check
  refine ⟨⟨run.steps,?_⟩,run.steps_le_m⟩
  have executed := iterate_map_some (rawRangeTranslated accepted tail)
    (fun step => rawRange_translateStep accepted tail step) run.steps run.evals_in_steps
  change (flip bind steinerRawRangeBatchMachine.step)^[run.steps]
      (some (rawRangeTranslated accepted tail (initList steinerBinaryComparisonMachine (encodeSteinerBinaryComparison check)))) =
    some (rawRangeTranslated accepted tail (haltList steinerBinaryComparisonMachine (steinerBinaryComparisonOutput check))) at executed
  rw [rawRange_compareInit,rawRange_compareReturn] at executed
  exact executed

private theorem rawRange_machineInit (tape : List SteinerRawRangeSymbol) :
    initList steinerRawRangeBatchMachine tape = rawRangeCfg (some (.collect true)) [] [] tape := by
  unfold initList rawRangeCfg
  apply congrArg (fun stk : Fin 4 → List SteinerRawRangeSymbol =>
    (⟨some (RawRangeLabel.collect true),rawRangeInitial,stk⟩ : steinerRawRangeBatchMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem rawRange_machineHalt (out : List SteinerRawRangeSymbol) :
    haltList steinerRawRangeBatchMachine out = rawRangeCfg none [] [] out := by
  unfold haltList rawRangeCfg
  apply congrArg (fun stk : Fin 4 → List SteinerRawRangeSymbol =>
    (⟨none,rawRangeInitial,stk⟩ : steinerRawRangeBatchMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private def rawRange_fold (checks : List SteinerRangeWordPair) (accepted : Bool) :
    EvalsToInTime steinerRawRangeBatchMachine.step
      (rawRangeCfg (some (.collect accepted)) [] [] (encodeSteinerRawRangeBatch checks))
      (some (rawRangeCfg none [] [] (encodeSteinerRawRangeAnswer (accepted && steinerRangeChecks checks))))
      (5*(encodeSteinerRawRangeBatch checks).length+1) := by
  induction checks generalizing accepted with
  | nil => simpa [encodeSteinerRawRangeBatch,steinerRangeChecks] using rawRangeOne (rawRange_batchDone accepted)
  | cons check checks ih =>
    let frame := encodeSteinerBinaryComparison check
    let pending := encodeSteinerRawRangeBatch checks
    let ordered := (binaryLessWithWork check.1 check.2 false).1
    let same := (binaryEqualWithWork check.1 check.2).1
    have collect := rawRange_collectFrame accepted frame [] pending
    rw [List.append_nil] at collect
    have restore := rawRange_restoreFrame accepted (frame.map some).reverse [] pending
    rw [List.reverse_reverse,List.append_nil,List.length_reverse,List.length_map] at restore
    have compare := rawRange_compareEval accepted check pending
    have record := rawRangeOne (rawRange_record accepted ordered same pending)
    have later := ih (accepted && ordered)
    have prepare := EvalsToInTime.trans _ _ _ _ _ _ collect restore
    have compareFirst := EvalsToInTime.trans _ _ _ _ _ _ prepare compare
    have finishFirst := EvalsToInTime.trans _ _ _ _ _ _ compareFirst record
    have whole := EvalsToInTime.trans _ _ _ _ _ _ finishFirst later
    have frameLength : frame.length = check.1.length+check.2.length+1 := by
      simp only [frame,encodeSteinerBinaryComparison,List.length_append,List.length_map,List.length_cons]
      omega
    have bound : whole.steps ≤ 5*(frame.length+1+pending.length)+1 := by
      have spent := whole.steps_le_m
      change whole.steps ≤ (5*pending.length+1)+(1+((3*check.1.length+check.2.length+3)+
        ((frame.length+1)+(frame.length+1)))) at spent
      omega
    have run : EvalsToInTime steinerRawRangeBatchMachine.step _ _ (5*(frame.length+1+pending.length)+1) :=
      ⟨whole.toEvalsTo,bound⟩
    simpa only [encodeSteinerRawRangeBatch,List.flatMap_cons,List.append_assoc,List.singleton_append,
      List.length_append,List.length_map,List.length_cons,List.length_nil,steinerRangeChecks,List.all_cons,
      Bool.and_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,frame,pending,ordered] using run

/-- Check every raw-word request and report their exact conjunction,
in at most five transitions per framed input symbol plus one. -/
def steinerRawRangeBatchMachine_run (checks : List SteinerRangeWordPair) :
    TM2OutputsInTime steinerRawRangeBatchMachine (encodeSteinerRawRangeBatch checks)
      (some (encodeSteinerRawRangeAnswer (steinerRangeChecks checks)))
      (5*(encodeSteinerRawRangeBatch checks).length+1) := by
  have run := rawRange_fold checks true
  simp only [Bool.true_and] at run
  change EvalsToInTime steinerRawRangeBatchMachine.step _ (some (haltList steinerRawRangeBatchMachine _)) _
  rw [rawRange_machineInit,rawRange_machineHalt]
  exact run

/-- A linear polynomial certificate for raw-word batches, including the empty batch. -/
noncomputable def steinerRawRangeBatchMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerRawRangeBatch encodeSteinerRawRangeAnswer steinerRangeChecks where
  tm := steinerRawRangeBatchMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 5*Polynomial.X+Polynomial.C 1
  outputsFun checks := by
    change TM2OutputsInTime steinerRawRangeBatchMachine ((encodeSteinerRawRangeBatch checks).map id)
      (some ((encodeSteinerRawRangeAnswer (steinerRangeChecks checks)).map id)) _
    simpa only [List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_X,
      Polynomial.eval_C] using steinerRawRangeBatchMachine_run checks

/-- For graph rows the input size counts raw endpoint bits, two copies
of the bound per row, and two separators per check. -/
theorem encodeSteinerRawRangeRequests_length (bound : List Bool) (rows : List SteinerRangeWordPair) :
    (encodeSteinerRawRangeBatch (steinerRangeRequests bound rows)).length =
      binaryEndpointBits rows+2*rows.length*(bound.length+2) := by
  induction rows with
  | nil => simp [encodeSteinerRawRangeBatch,steinerRangeRequests,binaryEndpointBits]
  | cons row rows ih =>
    simp only [encodeSteinerRawRangeBatch,steinerRangeRequests,List.flatMap_cons,List.cons_append,List.nil_append,
      List.length_append,List.length_map,List.length_nil,List.length_cons,encodeSteinerBinaryComparison,
      binaryEndpointBits,List.map_cons,List.sum_cons] at ih ⊢
    rw [Nat.mul_succ 2,Nat.add_mul]
    omega

/-- The machine computes the guarded decoder flag on the actual
variable-word width from the raw endpoint and supplied bound frames. -/
def steinerRawRangeBatchMachine_guardedGraph {n : ℕ} (bound : List Bool) (number : binaryWordValue bound = n)
    (rows : List SteinerRangeWordPair) :
    TM2OutputsInTime steinerRawRangeBatchMachine (encodeSteinerRawRangeBatch (steinerRangeRequests bound rows))
      (some (encodeSteinerRawRangeAnswer
        ((decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1.isSome)))
      (5*(binaryEndpointBits rows+2*rows.length*(bound.length+2))+1) := by
  rw [← steinerRangeRequests_guarded_flag bound number rows,← encodeSteinerRawRangeRequests_length]
  exact steinerRawRangeBatchMachine_run _

end OnlineReachabilityPreservers
