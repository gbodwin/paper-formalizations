import OnlineReachabilityPreservers.SteinerBinaryComparisonMachine
import OnlineReachabilityPreservers.SteinerForestScaleDistanceRounds
import OnlineReachabilityPreservers.SteinerStackFrame
import OnlineReachabilityPreservers.SteinerStackReturn

/-! Add a transfer weight and earlier rooted weight exactly when the transfer fits the cap. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev CappedSumCompareLabel := steinerBinaryComparisonMachine.Λ
private abbrev CappedSumCompareRegister := steinerBinaryComparisonMachine.σ
private instance : Fintype CappedSumCompareLabel := steinerBinaryComparisonMachine.ΛFin

private inductive CappedSumLabel where
  | bound
  | distance
  | compare (label : CappedSumCompareLabel)
  | select
  | add
  | discard
  | clear
  deriving Fintype

private abbrev CappedSumSymbol := Option Bool
private abbrev CappedSumRegister := Option CappedSumSymbol × CappedSumCompareRegister
private abbrev CappedSumProgram := StackMachineTag.Program (Fin 5) CappedSumSymbol CappedSumLabel CappedSumRegister

private def cappedSumInitial : CappedSumRegister := (none,steinerBinaryComparisonMachine.initialState)

private def cappedSumObserve (_ : CappedSumRegister) (value : Option CappedSumSymbol) : CappedSumRegister :=
  (value,steinerBinaryComparisonMachine.initialState)

private def cappedSumNext (label : CappedSumLabel) : CappedSumProgram :=
  load (fun _ => cappedSumInitial) (goto (fun _ => label))

private def cappedSumTag :
    StackMachineTag CappedSumSymbol CappedSumSymbol CappedSumCompareLabel CappedSumLabel
      CappedSumCompareRegister CappedSumRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (none,r)
  readRegister := Prod.snd
  writeLabel := .compare
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def cappedSumSlots : Fin 3 ↪ Fin 5 :=
  ⟨fun i => i.castSucc.castSucc,(Fin.castSucc_injective 4).comp (Fin.castSucc_injective 3)⟩

private def cappedSumCompareInner :
    CappedSumLabel → StackMachineTag.Program (Fin 3) CappedSumSymbol CappedSumLabel CappedSumRegister
  | .compare label => cappedSumTag.returningStatement .select (steinerBinaryComparisonMachine.m label)
  | _ => halt

private def cappedSumProgram : CappedSumLabel → CappedSumProgram
  | .bound =>
    pop 4 cappedSumObserve <|
      branch (fun r => r.1.join.isSome)
        (push 0 (fun _ => some true) (cappedSumNext .bound))
        (push 0 (fun _ => some true) <|
          push 0 (fun _ => none) (cappedSumNext .distance))
  | .distance =>
    pop 4 cappedSumObserve <|
      branch (fun r => r.1.join.isSome)
        (push 0 (fun _ => some true) <|
          push 3 (fun _ => some true) (cappedSumNext .distance))
        (cappedSumNext (.compare steinerBinaryComparisonMachine.main))
  | .compare label => StackIndexEmbedding.statement cappedSumSlots (cappedSumCompareInner (.compare label))
  | .select =>
    pop 0 cappedSumObserve <|
      pop 0 (fun r _ => r) <|
      branch (fun r => r.1 == some (some true)) (cappedSumNext .add) (cappedSumNext .discard)
  | .add =>
    pop 4 cappedSumObserve <|
      branch (fun r => r.1.isSome)
        (push 3 (fun _ => some true) (cappedSumNext .add))
        (load (fun _ => cappedSumInitial) halt)
  | .discard =>
    pop 3 cappedSumObserve <|
      branch (fun r => r.1.isSome) (cappedSumNext .discard) (cappedSumNext .clear)
  | .clear =>
    pop 4 cappedSumObserve <|
      branch (fun r => r.1.isSome) (cappedSumNext .clear) (load (fun _ => cappedSumInitial) halt)

/-- The supplied cap and distance are unary. Use the existing binary
comparator on all-one words, preserving the distance tallies separately. -/
abbrev steinerUnaryCappedSumMachine : FinTM2 where
  K := Fin 5
  k₀ := 4
  k₁ := 3
  Γ _ := CappedSumSymbol
  Λ := CappedSumLabel
  main := .bound
  σ := CappedSumRegister
  initialState := cappedSumInitial
  m := cappedSumProgram

private def cappedSumCfg (label : Option CappedSumLabel) (cmp out input : List CappedSumSymbol) :
    steinerUnaryCappedSumMachine.Cfg where
  l := label
  var := cappedSumInitial
  stk := ![cmp,[],[],out,input]

private theorem cappedSum_update0 (c o i w : List CappedSumSymbol) :
    Function.update (![c,[],[],o,i] : Fin 5 → List CappedSumSymbol) 0 w = ![w,[],[],o,i] := by
  funext slot
  fin_cases slot <;> simp [Function.update]

private theorem cappedSum_update3 (c o i w : List CappedSumSymbol) :
    Function.update (![c,[],[],o,i] : Fin 5 → List CappedSumSymbol) 3 w = ![c,[],[],w,i] := by
  funext slot
  fin_cases slot <;> simp [Function.update]

private theorem cappedSum_update4 (c o i w : List CappedSumSymbol) :
    Function.update (![c,[],[],o,i] : Fin 5 → List CappedSumSymbol) 4 w = ![c,[],[],o,w] := by
  funext slot
  fin_cases slot <;> simp [Function.update]

private def cappedSum_one {a b : steinerUnaryCappedSumMachine.Cfg}
    (move : steinerUnaryCappedSumMachine.step a = some b) :
    EvalsToInTime steinerUnaryCappedSumMachine.step a (some b) 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := move

private def cappedTallies (n : ℕ) : List CappedSumSymbol := List.replicate n (some true)

private theorem cappedTallies_append (n : ℕ) (tail : List CappedSumSymbol) :
    cappedTallies n++some true::tail = cappedTallies (n+1)++tail := by
  simp only [cappedTallies,List.replicate_add,List.replicate_one,List.append_assoc,List.singleton_append]

private theorem cappedSum_boundTally (cmp input : List CappedSumSymbol) :
    steinerUnaryCappedSumMachine.step (cappedSumCfg (some .bound) cmp [] (some true::input)) =
      some (cappedSumCfg (some .bound) (some true::cmp) [] input) := by
  simp [FinTM2.step,steinerUnaryCappedSumMachine,cappedSumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedSumProgram,cappedSumObserve,cappedSumNext,cappedSum_update0,cappedSum_update4]
  rfl

private theorem cappedSum_boundEnd (cmp input : List CappedSumSymbol) :
    steinerUnaryCappedSumMachine.step (cappedSumCfg (some .bound) cmp [] (none::input)) =
      some (cappedSumCfg (some .distance) (none::some true::cmp) [] input) := by
  simp [FinTM2.step,steinerUnaryCappedSumMachine,cappedSumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedSumProgram,cappedSumObserve,cappedSumNext,cappedSum_update0,cappedSum_update4]
  rfl

private def cappedSum_bound (n : ℕ) (cmp input : List CappedSumSymbol) :
    EvalsToInTime steinerUnaryCappedSumMachine.step
      (cappedSumCfg (some .bound) cmp [] (cappedTallies n++none::input))
      (some (cappedSumCfg (some .distance) (none::(cappedTallies (n+1)++cmp)) [] input)) (n+1) := by
  induction n generalizing cmp with
  | zero => exact cappedSum_one (cappedSum_boundEnd cmp input)
  | succ n ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _
      (cappedSum_one (cappedSum_boundTally cmp (cappedTallies n++none::input))) (ih (some true::cmp))
    rw [cappedTallies_append] at all
    exact all

private theorem cappedSum_distanceTally (cmp out input : List CappedSumSymbol) :
    steinerUnaryCappedSumMachine.step (cappedSumCfg (some .distance) cmp out (some true::input)) =
      some (cappedSumCfg (some .distance) (some true::cmp) (some true::out) input) := by
  simp [FinTM2.step,steinerUnaryCappedSumMachine,cappedSumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedSumProgram,cappedSumObserve,cappedSumNext,cappedSum_update0,cappedSum_update3,cappedSum_update4]
  rfl

private theorem cappedSum_distanceEnd (cmp out input : List CappedSumSymbol) :
    steinerUnaryCappedSumMachine.step (cappedSumCfg (some .distance) cmp out (none::input)) =
      some (cappedSumCfg (some (.compare steinerBinaryComparisonMachine.main)) cmp out input) := by
  simp [FinTM2.step,steinerUnaryCappedSumMachine,cappedSumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedSumProgram,cappedSumObserve,cappedSumNext,cappedSum_update4]
  rfl

private def cappedSum_distance (d : ℕ) (cmp out input : List CappedSumSymbol) :
    EvalsToInTime steinerUnaryCappedSumMachine.step
      (cappedSumCfg (some .distance) cmp out (cappedTallies d++none::input))
      (some (cappedSumCfg (some (.compare steinerBinaryComparisonMachine.main))
        (cappedTallies d++cmp) (cappedTallies d++out) input)) (d+1) := by
  induction d generalizing cmp out with
  | zero => exact cappedSum_one (cappedSum_distanceEnd cmp out input)
  | succ d ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _
      (cappedSum_one (cappedSum_distanceTally cmp out (cappedTallies d++none::input)))
      (ih (some true::cmp) (some true::out))
    rw [cappedTallies_append,cappedTallies_append] at all
    exact all

private theorem cappedSum_true_word_value (n : ℕ) :
    binaryWordValue (List.replicate n true)+1 = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 1+2*binaryWordValue (List.replicate n true)+1 = 2^(n+1)
    rw [pow_succ]
    omega

private theorem cappedSum_unary_le (d n : ℕ) :
    binaryWordValue (List.replicate d true) < binaryWordValue (List.replicate (n+1) true) ↔ d ≤ n := by
  have left := cappedSum_true_word_value d
  have right := cappedSum_true_word_value (n+1)
  constructor
  · intro lt
    by_contra! large
    have order := Nat.pow_le_pow_right (by decide : 0 < 2) (show n+1 ≤ d by omega)
    omega
  · intro fit
    have order := Nat.pow_lt_pow_right (by decide : 1 < 2) (show d < n+1 by omega)
    omega

private def cappedSum_compare_input (d n : ℕ) : List CappedSumSymbol :=
  cappedTallies d++none::cappedTallies (n+1)

private def cappedSum_comparisonRun (d n : ℕ) :
    TM2OutputsInTime steinerBinaryComparisonMachine (cappedSum_compare_input d n)
      (some [some (decide (d≤n)),some (decide (List.replicate d true = List.replicate (n+1) true))]) (3*d+n+4) := by
  let words := (List.replicate d true,List.replicate (n+1) true)
  have run := steinerBinaryComparisonMachine_run words
  rw [steinerBinaryComparisonOutput_spec] at run
  simpa only [words,Prod.fst,Prod.snd,cappedSum_unary_le,encodeSteinerBinaryComparison,List.map_replicate,
    List.length_replicate,cappedSum_compare_input,cappedTallies,Nat.add_assoc] using run

private def cappedSumPassive (out input : List CappedSumSymbol) (slot : Fin 5) : List CappedSumSymbol :=
  if slot = 3 then out else if slot = 4 then input else []

private noncomputable def cappedSumTranslated (out input : List CappedSumSymbol) (c : steinerBinaryComparisonMachine.Cfg) :
    steinerUnaryCappedSumMachine.Cfg :=
  StackIndexEmbedding.configuration cappedSumSlots (cappedSumPassive out input)
    (cappedSumTag.returningConfiguration .select c)

private theorem cappedSum_compareStep (out input : List CappedSumSymbol) {c after : steinerBinaryComparisonMachine.Cfg}
    (move : steinerBinaryComparisonMachine.step c = some after) :
    steinerUnaryCappedSumMachine.step (cappedSumTranslated out input c) = some (cappedSumTranslated out input after) := by
  have tagged := cappedSumTag.step_embedded_return .select (base := steinerBinaryComparisonMachine.m)
    (host := cappedSumCompareInner) (fun _ => rfl) move
  have framed := StackIndexEmbedding.step_on cappedSumSlots (base := cappedSumCompareInner)
    (cappedSumPassive out input) (cappedSumTag.returningConfiguration .select c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem cappedSum_compareTapes (cmp out input : List CappedSumSymbol) (c : steinerBinaryComparisonMachine.Cfg)
    (tapes : c.stk = ![cmp,[],[]]) :
    (cappedSumTranslated out input c).stk = ![cmp,[],[],out,input] := by
  have image (i : Fin 3) : (cappedSumTranslated out input c).stk (cappedSumSlots i) =
      (![cmp,[],[]] : Fin 3 → List CappedSumSymbol) i := by
    change StackIndexEmbedding.tapesAt cappedSumSlots (fun k => (c.stk k).map id) (cappedSumPassive out input)
      (cappedSumSlots i) = _
    rw [StackIndexEmbedding.tapesAt_image,List.map_id,tapes]
  have extra (i : Fin 5) (absent : ∀ j, cappedSumSlots j ≠ i) :
      (cappedSumTranslated out input c).stk i = cappedSumPassive out input i :=
    StackIndexEmbedding.tapesAt_extra cappedSumSlots _ _ absent
  funext i
  fin_cases i
  · exact image 0
  · exact image 1
  · exact image 2
  · exact extra 3 (by intro j; fin_cases j <;> decide)
  · exact extra 4 (by intro j; fin_cases j <;> decide)

private theorem cappedSum_compareInit (cmp out input : List CappedSumSymbol) :
    cappedSumTranslated out input (initList steinerBinaryComparisonMachine cmp) =
      cappedSumCfg (some (.compare steinerBinaryComparisonMachine.main)) cmp out input := by
  apply congrArg (fun stk : Fin 5 → List CappedSumSymbol =>
    (⟨some (.compare steinerBinaryComparisonMachine.main),cappedSumInitial,stk⟩ : steinerUnaryCappedSumMachine.Cfg))
  apply cappedSum_compareTapes
  funext i
  fin_cases i <;> rfl

private theorem cappedSum_compareReturn (cmp out input : List CappedSumSymbol) :
    cappedSumTranslated out input (haltList steinerBinaryComparisonMachine cmp) =
      cappedSumCfg (some .select) cmp out input := by
  apply congrArg (fun stk : Fin 5 → List CappedSumSymbol =>
    (⟨some .select,cappedSumInitial,stk⟩ : steinerUnaryCappedSumMachine.Cfg))
  apply cappedSum_compareTapes
  funext i
  fin_cases i <;> rfl

private def cappedSum_compare {time : ℕ} (cmp flags out input : List CappedSumSymbol)
    (run : TM2OutputsInTime steinerBinaryComparisonMachine cmp (some flags) time) :
    EvalsToInTime steinerUnaryCappedSumMachine.step
      (cappedSumCfg (some (.compare steinerBinaryComparisonMachine.main)) cmp out input)
      (some (cappedSumCfg (some .select) flags out input)) time := by
  refine ⟨⟨run.steps,?_⟩,run.steps_le_m⟩
  have all := iterate_map_some (cappedSumTranslated out input) (fun move => cappedSum_compareStep out input move)
    run.steps run.evals_in_steps
  change (flip bind steinerUnaryCappedSumMachine.step)^[run.steps]
    (some (cappedSumTranslated out input (initList steinerBinaryComparisonMachine cmp))) =
    some (cappedSumTranslated out input (haltList steinerBinaryComparisonMachine flags)) at all
  rwa [cappedSum_compareInit,cappedSum_compareReturn] at all

private theorem cappedSum_selectStep (fit equal : Bool) (out input : List CappedSumSymbol) :
    steinerUnaryCappedSumMachine.step (cappedSumCfg (some .select) [some fit,some equal] out input) =
      some (cappedSumCfg (some (if fit then .add else .discard)) [] out input) := by
  cases fit <;>
    simp [FinTM2.step,steinerUnaryCappedSumMachine,cappedSumCfg,Turing.TM2.step,Turing.TM2.stepAux,
      cappedSumProgram,cappedSumObserve,cappedSumNext,cappedSum_update0] <;> rfl

private theorem cappedSum_addTally (out input : List CappedSumSymbol) :
    steinerUnaryCappedSumMachine.step (cappedSumCfg (some .add) [] out (some true::input)) =
      some (cappedSumCfg (some .add) [] (some true::out) input) := by
  simp [FinTM2.step,steinerUnaryCappedSumMachine,cappedSumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedSumProgram,cappedSumObserve,cappedSumNext,cappedSum_update3,cappedSum_update4]
  rfl

private theorem cappedSum_addEnd (out : List CappedSumSymbol) :
    steinerUnaryCappedSumMachine.step (cappedSumCfg (some .add) [] out []) = some (cappedSumCfg none [] out []) := by
  simp [FinTM2.step,steinerUnaryCappedSumMachine,cappedSumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedSumProgram,cappedSumObserve,cappedSum_update4]
  rfl

private def cappedSum_add (amount : ℕ) (out : List CappedSumSymbol) :
    EvalsToInTime steinerUnaryCappedSumMachine.step (cappedSumCfg (some .add) [] out (cappedTallies amount))
      (some (cappedSumCfg none [] (cappedTallies amount++out) [])) (amount+1) := by
  induction amount generalizing out with
  | zero => exact cappedSum_one (cappedSum_addEnd out)
  | succ amount ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _
      (cappedSum_one (cappedSum_addTally out (cappedTallies amount))) (ih (some true::out))
    rw [cappedTallies_append] at all
    exact all

private theorem cappedSum_discardSymbol (symbol : CappedSumSymbol) (out input : List CappedSumSymbol) :
    steinerUnaryCappedSumMachine.step (cappedSumCfg (some .discard) [] (symbol::out) input) =
      some (cappedSumCfg (some .discard) [] out input) := by
  simp [FinTM2.step,steinerUnaryCappedSumMachine,cappedSumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedSumProgram,cappedSumObserve,cappedSumNext,cappedSum_update3]
  rfl

private theorem cappedSum_discardEnd (input : List CappedSumSymbol) :
    steinerUnaryCappedSumMachine.step (cappedSumCfg (some .discard) [] [] input) =
      some (cappedSumCfg (some .clear) [] [] input) := by
  simp [FinTM2.step,steinerUnaryCappedSumMachine,cappedSumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedSumProgram,cappedSumObserve,cappedSumNext,cappedSum_update3]
  rfl

private def cappedSum_discard (out input : List CappedSumSymbol) :
    EvalsToInTime steinerUnaryCappedSumMachine.step (cappedSumCfg (some .discard) [] out input)
      (some (cappedSumCfg (some .clear) [] [] input)) (out.length+1) := by
  induction out with
  | nil => exact cappedSum_one (cappedSum_discardEnd input)
  | cons symbol out ih =>
    exact EvalsToInTime.trans _ _ _ _ _ _ (cappedSum_one (cappedSum_discardSymbol symbol out input)) ih

private theorem cappedSum_clearSymbol (symbol : CappedSumSymbol) (input : List CappedSumSymbol) :
    steinerUnaryCappedSumMachine.step (cappedSumCfg (some .clear) [] [] (symbol::input)) =
      some (cappedSumCfg (some .clear) [] [] input) := by
  simp [FinTM2.step,steinerUnaryCappedSumMachine,cappedSumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedSumProgram,cappedSumObserve,cappedSumNext,cappedSum_update4]
  rfl

private theorem cappedSum_clearEnd :
    steinerUnaryCappedSumMachine.step (cappedSumCfg (some .clear) [] [] []) = some (cappedSumCfg none [] [] []) := by
  simp [FinTM2.step,steinerUnaryCappedSumMachine,cappedSumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    cappedSumProgram,cappedSumObserve,cappedSum_update4]
  rfl

private def cappedSum_clear (input : List CappedSumSymbol) :
    EvalsToInTime steinerUnaryCappedSumMachine.step (cappedSumCfg (some .clear) [] [] input)
      (some (cappedSumCfg none [] [] [])) (input.length+1) := by
  induction input with
  | nil => exact cappedSum_one cappedSum_clearEnd
  | cons symbol input ih =>
    exact EvalsToInTime.trans _ _ _ _ _ _ (cappedSum_one (cappedSum_clearSymbol symbol input)) ih

private theorem cappedSum_init (word : List CappedSumSymbol) :
    initList steinerUnaryCappedSumMachine word = cappedSumCfg (some .bound) [] [] word := by
  apply congrArg (fun stk : Fin 5 → List CappedSumSymbol =>
    (⟨some .bound,cappedSumInitial,stk⟩ : steinerUnaryCappedSumMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem cappedSum_halt (out : List CappedSumSymbol) :
    haltList steinerUnaryCappedSumMachine out = cappedSumCfg none [] out [] := by
  apply congrArg (fun stk : Fin 5 → List CappedSumSymbol =>
    (⟨none,cappedSumInitial,stk⟩ : steinerUnaryCappedSumMachine.Cfg))
  funext i
  fin_cases i <;> rfl

abbrev SteinerUnaryCappedSumRequest := ℕ × ℕ × ℕ

/-- The cap, distance and earlier weight are framed as unary operands. -/
def encodeSteinerUnaryCappedSum (request : SteinerUnaryCappedSumRequest) : List (Option Bool) :=
  cappedTallies request.1++none::(cappedTallies request.2.1++none::cappedTallies request.2.2)

private def cappedSum_beforeSelect (n d s : ℕ) :
    EvalsToInTime steinerUnaryCappedSumMachine.step
      (initList steinerUnaryCappedSumMachine (encodeSteinerUnaryCappedSum (n,d,s)))
      (some (cappedSumCfg (some .select) [some (decide (d≤n)),
        some (decide (List.replicate d true = List.replicate (n+1) true))] (cappedTallies d) (cappedTallies s)))
      (2*n+4*d+6) := by
  have bound := cappedSum_bound n [] (cappedTallies d++none::cappedTallies s)
  simp only [List.append_nil] at bound
  have dist := cappedSum_distance d (none::cappedTallies (n+1)) [] (cappedTallies s)
  simp only [List.append_nil] at dist
  have prepared := EvalsToInTime.trans _ _ _ _ _ _ bound dist
  have checked := cappedSum_compare _ _ (cappedTallies d) (cappedTallies s) (cappedSum_comparisonRun d n)
  have all := EvalsToInTime.trans _ _ _ _ _ _ prepared checked
  rw [cappedSum_init]
  exact ⟨all.toEvalsTo,by have spent := all.steps_le_m; omega⟩

/-- A distance at or below the cap contributes its value plus the
earlier weight. Equality at the cap is included. -/
def steinerUnaryCappedSumMachine_accepted (n d s : ℕ) (fit : d ≤ n) :
    TM2OutputsInTime steinerUnaryCappedSumMachine (encodeSteinerUnaryCappedSum (n,d,s))
      (some (cappedTallies (d+s))) (2*n+4*d+s+8) := by
  have loaded := cappedSum_beforeSelect n d s
  simp only [fit,decide_true] at loaded
  have selected := cappedSum_one (cappedSum_selectStep true
    (decide (List.replicate d true = List.replicate (n+1) true)) (cappedTallies d) (cappedTallies s))
  have checked := EvalsToInTime.trans _ _ _ _ _ _ loaded selected
  have written := cappedSum_add s (cappedTallies d)
  have unary : cappedTallies s++cappedTallies d = cappedTallies (d+s) := by
    simp only [cappedTallies,add_comm d s,List.replicate_add]
  rw [unary] at written
  have all := EvalsToInTime.trans _ _ _ _ _ _ checked written
  change EvalsToInTime steinerUnaryCappedSumMachine.step _ (some (haltList _ _)) _
  rw [cappedSum_halt]
  exact ⟨all.toEvalsTo,by have spent := all.steps_le_m; omega⟩

/-- A distance above the cap contributes zero. Both operand archives
are cleared in this branch. -/
def steinerUnaryCappedSumMachine_rejected (n d s : ℕ) (outside : n < d) :
    TM2OutputsInTime steinerUnaryCappedSumMachine (encodeSteinerUnaryCappedSum (n,d,s))
      (some []) (2*n+5*d+s+9) := by
  have loaded := cappedSum_beforeSelect n d s
  simp only [Nat.not_le.mpr outside,decide_false] at loaded
  have selected := cappedSum_one (cappedSum_selectStep false
    (decide (List.replicate d true = List.replicate (n+1) true)) (cappedTallies d) (cappedTallies s))
  have checked := EvalsToInTime.trans _ _ _ _ _ _ loaded selected
  have discarded := EvalsToInTime.trans _ _ _ _ _ _ checked (cappedSum_discard (cappedTallies d) (cappedTallies s))
  have all := EvalsToInTime.trans _ _ _ _ _ _ discarded (cappedSum_clear (cappedTallies s))
  change EvalsToInTime steinerUnaryCappedSumMachine.step _ (some (haltList _ _)) _
  rw [cappedSum_halt]
  refine ⟨all.toEvalsTo,?_⟩
  have spent := all.steps_le_m
  simp only [cappedTallies,List.length_replicate] at spent
  omega

/-- A capped transfer contributes its distance plus the earlier weight
when the distance is at most the cap. -/
def steinerUnaryCappedSum (request : SteinerUnaryCappedSumRequest) : ℕ :=
  if request.2.1 ≤ request.1 then request.2.1+request.2.2 else 0

/-- The unary contribution of a capped transfer. -/
def steinerUnaryCappedSumAnswer (request : SteinerUnaryCappedSumRequest) : List (Option Bool) :=
  cappedTallies (steinerUnaryCappedSum request)

theorem encodeSteinerUnaryCappedSum_length (n d s : ℕ) :
    (encodeSteinerUnaryCappedSum (n,d,s)).length = n+d+s+2 := by
  simp only [encodeSteinerUnaryCappedSum,cappedTallies,List.length_append,List.length_replicate,List.length_cons]
  omega

/-- Both outcomes take linear time in the input length. -/
def steinerUnaryCappedSumMachine_run (request : SteinerUnaryCappedSumRequest) :
    let X := (encodeSteinerUnaryCappedSum request).length
    TM2OutputsInTime steinerUnaryCappedSumMachine (encodeSteinerUnaryCappedSum request)
      (some (steinerUnaryCappedSumAnswer request)) (5*X+1) := by
  obtain ⟨n,d,s⟩ := request
  dsimp only
  rw [encodeSteinerUnaryCappedSum_length]
  unfold steinerUnaryCappedSumAnswer steinerUnaryCappedSum
  dsimp only
  by_cases fit : d ≤ n
  · rw [ite_eq_left fit]
    let run := steinerUnaryCappedSumMachine_accepted n d s fit
    exact ⟨run.toEvalsTo,run.steps_le_m.trans (by omega)⟩
  · rw [ite_eq_right fit]
    let run := steinerUnaryCappedSumMachine_rejected n d s (Nat.lt_of_not_ge fit)
    exact ⟨run.toEvalsTo,run.steps_le_m.trans (by omega)⟩

/-- Linear-time computation of the conditional unary sum. -/
noncomputable def steinerUnaryCappedSumMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryCappedSum id steinerUnaryCappedSumAnswer where
  tm := steinerUnaryCappedSumMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 5*Polynomial.X+Polynomial.C 1
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,
      Polynomial.eval_X,Polynomial.eval_C] using steinerUnaryCappedSumMachine_run request


/-- Select one distance and the prior rooted weight used by an inward round. -/
def steinerForestTransferSumRequest {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ)
    (child root : Fin n) : SteinerUnaryCappedSumRequest :=
  (n,dist (child,root),(inwardHeightWeightRounds dist h)[child.val])

/-- The same actual machine computes the contribution at a specified
position of the distance table when given its three unary operands. -/
def steinerUnaryCappedSumMachine_forestTransfer {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ)
    (child root : Fin n) :
    let prior := (inwardHeightWeightRounds dist h)[child.val]
    let d := dist (child,root)
    let input := encodeSteinerUnaryCappedSum (steinerForestTransferSumRequest dist h child root)
    TM2OutputsInTime steinerUnaryCappedSumMachine input
      (some (List.replicate (if d ≤ n then d+prior else 0) (some true))) (5*input.length+1) := by
  exact steinerUnaryCappedSumMachine_run (steinerForestTransferSumRequest dist h child root)

private theorem cappedSum_hops_le {n : ℕ} (G : Arcs (Fin n)) (v r : Fin n) :
    hops G v r ≤ n+1 := by
  let levels := (Finset.range (Fintype.card (Fin n)+1)).filter (fun d => v ∈ reachIn G r d)
  change (least? levels).getD (Fintype.card (Fin n)+1) ≤ n+1
  cases found : least? levels with
  | none => simp only [Option.getD_none,Fintype.card_fin]; exact le_rfl
  | some depth =>
    have member := least?_mem found
    change depth ∈ (Finset.range (Fintype.card (Fin n)+1)).filter (fun d => v ∈ reachIn G r d) at member
    have inside := Finset.mem_range.mp (Finset.mem_filter.mp member).1
    simp only [Fintype.card_fin] at inside
    exact inside.le

/-- A correct hop table, including its unreachable marker, gives a
polynomial bound on the unary operand frame at fixed height. -/
theorem encodeSteinerForestTransferSum_length_le {n : ℕ} (G : Arcs (Fin n)) (dist : Fin n × Fin n → ℕ)
    (values : ∀ e, dist e = hops G e.1 e.2) (h : ℕ) (child root : Fin n) :
    (encodeSteinerUnaryCappedSum (steinerForestTransferSumRequest dist h child root)).length ≤
      2*n+inwardHeightWeightRoundBound n h+3 := by
  have distance : dist (child,root) ≤ n+1 := (values (child,root)).trans_le (cappedSum_hops_le G child root)
  have prior := inwardHeightWeightRounds_get_le dist h child
  rw [steinerForestTransferSumRequest,encodeSteinerUnaryCappedSum_length]
  omega

end OnlineReachabilityPreservers
