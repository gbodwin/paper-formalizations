import OnlineReachabilityPreservers.SteinerUnaryArcCountMachine

/-! Generate the ordered unary frame of all directed candidate arcs. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private inductive ArcEnumSide where
  | source
  | target
  deriving DecidableEq

private instance : Fintype ArcEnumSide where
  elems := {.source,.target}
  complete := by intro side; cases side <;> simp

private inductive ArcEnumLabel where
  | loadBound
  | nextSource
  | cloneBound
  | restoreBound
  | nextTarget
  | write (side : ArcEnumSide)
  | restore (side : ArcEnumSide)
  | clearBound
  deriving Fintype

private abbrev ArcEnumRegister := Option (Option Bool)
private abbrev ArcEnumProgram := StackMachineTag.Program (Fin 5) (Option Bool) ArcEnumLabel ArcEnumRegister

private def arcEnumNext (label : ArcEnumLabel) : ArcEnumProgram :=
  load (fun _ => none) (goto (fun _ => label))

private def arcEnumSlot : ArcEnumSide → Fin 5
  | .source => 2
  | .target => 3

private def arcEnumAfterRestore : ArcEnumSide → ArcEnumProgram
  | .source => arcEnumNext .nextTarget
  | .target => push 0 (fun _ => none) (arcEnumNext (.write .source))

private def arcEnumProgram : ArcEnumLabel → ArcEnumProgram
  | .loadBound =>
    pop 0 (fun _ seen => seen) <|
      branch Option.isSome
        (push 1 (fun _ => some true) (push 2 (fun _ => some true) (arcEnumNext .loadBound)))
        (arcEnumNext .nextSource)
  | .nextSource =>
    pop 2 (fun _ seen => seen) <|
      branch Option.isSome (arcEnumNext .cloneBound) (arcEnumNext .clearBound)
  | .cloneBound =>
    pop 1 (fun _ seen => seen) <|
      branch Option.isSome
        (push 3 (fun _ => some true) (push 4 (fun _ => some true) (arcEnumNext .cloneBound)))
        (arcEnumNext .restoreBound)
  | .restoreBound =>
    pop 4 (fun _ seen => seen) <|
      branch Option.isSome (push 1 (fun _ => some true) (arcEnumNext .restoreBound)) (arcEnumNext .nextTarget)
  | .nextTarget =>
    pop 3 (fun _ seen => seen) <|
      branch Option.isSome
        (push 0 (fun _ => none) (arcEnumNext (.write .target)))
        (arcEnumNext .nextSource)
  | .write side =>
    pop (arcEnumSlot side) (fun _ seen => seen) <|
      branch Option.isSome
        (push 0 (fun _ => some true) (push 4 (fun _ => some true) (arcEnumNext (.write side))))
        (arcEnumNext (.restore side))
  | .restore side =>
    pop 4 (fun _ seen => seen) <|
      branch Option.isSome
        (push (arcEnumSlot side) (fun _ => some true) (arcEnumNext (.restore side)))
        (arcEnumAfterRestore side)
  | .clearBound =>
    pop 1 (fun _ seen => seen) <|
      branch Option.isSome (arcEnumNext .clearBound) (load (fun _ => none) halt)

/-- Count both indices down and prepend each framed pair. The returned
rows are in increasing source and target order. -/
abbrev steinerUnaryArcEnumerationMachine : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 0
  Γ _ := Option Bool
  Λ := ArcEnumLabel
  main := .loadBound
  σ := ArcEnumRegister
  initialState := none
  m := arcEnumProgram

private abbrev enumTallies (n : ℕ) : List (Option Bool) := List.replicate n (some true)

private def arcEnumCfg (label : Option ArcEnumLabel) (frame : List (Option Bool)) (size source target used : ℕ) :
    steinerUnaryArcEnumerationMachine.Cfg where
  l := label
  var := none
  stk := ![frame,enumTallies size,enumTallies source,enumTallies target,enumTallies used]

private theorem arcEnum_update0 (a b c d e next : List (Option Bool)) :
    Function.update (![a,b,c,d,e] : Fin 5 → List (Option Bool)) 0 next = ![next,b,c,d,e] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem arcEnum_update1 (a b c d e next : List (Option Bool)) :
    Function.update (![a,b,c,d,e] : Fin 5 → List (Option Bool)) 1 next = ![a,next,c,d,e] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem arcEnum_update2 (a b c d e next : List (Option Bool)) :
    Function.update (![a,b,c,d,e] : Fin 5 → List (Option Bool)) 2 next = ![a,b,next,d,e] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem arcEnum_update3 (a b c d e next : List (Option Bool)) :
    Function.update (![a,b,c,d,e] : Fin 5 → List (Option Bool)) 3 next = ![a,b,c,next,e] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem arcEnum_update4 (a b c d e next : List (Option Bool)) :
    Function.update (![a,b,c,d,e] : Fin 5 → List (Option Bool)) 4 next = ![a,b,c,d,next] := by
  funext i
  fin_cases i <;> simp [Function.update]

private def arcEnum_one {a b : steinerUnaryArcEnumerationMachine.Cfg}
    (step : steinerUnaryArcEnumerationMachine.step a = some b) :
    EvalsToInTime steinerUnaryArcEnumerationMachine.step a (some b) 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := step

private theorem arcEnum_loadSymbol (input : List (Option Bool)) (size source : ℕ) :
    steinerUnaryArcEnumerationMachine.step (arcEnumCfg (some .loadBound) (some true::input) size source 0 0) =
      some (arcEnumCfg (some .loadBound) input (size+1) (source+1) 0 0) := by
  simp [FinTM2.step,steinerUnaryArcEnumerationMachine,arcEnumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcEnumProgram,arcEnumNext,arcEnum_update0,arcEnum_update1,arcEnum_update2,List.replicate_succ]
  rfl

private theorem arcEnum_loadEnd (size source : ℕ) :
    steinerUnaryArcEnumerationMachine.step (arcEnumCfg (some .loadBound) [] size source 0 0) =
      some (arcEnumCfg (some .nextSource) [] size source 0 0) := by
  simp [FinTM2.step,steinerUnaryArcEnumerationMachine,arcEnumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcEnumProgram,arcEnumNext,arcEnum_update0]
  rfl

private def arcEnum_load (tallies size source : ℕ) :
    EvalsToInTime steinerUnaryArcEnumerationMachine.step
      (arcEnumCfg (some .loadBound) (enumTallies tallies) size source 0 0)
      (some (arcEnumCfg (some .nextSource) [] (size+tallies) (source+tallies) 0 0)) (tallies+1) := by
  induction tallies generalizing size source with
  | zero => simpa only [List.replicate_zero,Nat.add_zero] using arcEnum_one (arcEnum_loadEnd size source)
  | succ tallies ih =>
    have first := arcEnum_one (arcEnum_loadSymbol (enumTallies tallies) size source)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (size+1) (source+1))
    have count (n : ℕ) : n+1+tallies = n+(tallies+1) := by omega
    simpa only [List.replicate_succ,count] using all

private theorem arcEnum_startSource (out : List (Option Bool)) (size source : ℕ) :
    steinerUnaryArcEnumerationMachine.step (arcEnumCfg (some .nextSource) out size (source+1) 0 0) =
      some (arcEnumCfg (some .cloneBound) out size source 0 0) := by
  simp [FinTM2.step,steinerUnaryArcEnumerationMachine,arcEnumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcEnumProgram,arcEnumNext,arcEnum_update2,List.replicate_succ]
  rfl

private theorem arcEnum_endSources (out : List (Option Bool)) (size : ℕ) :
    steinerUnaryArcEnumerationMachine.step (arcEnumCfg (some .nextSource) out size 0 0 0) =
      some (arcEnumCfg (some .clearBound) out size 0 0 0) := by
  simp [FinTM2.step,steinerUnaryArcEnumerationMachine,arcEnumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcEnumProgram,arcEnumNext,arcEnum_update2]
  rfl

private theorem arcEnum_cloneSymbol (out : List (Option Bool)) (size source target used : ℕ) :
    steinerUnaryArcEnumerationMachine.step (arcEnumCfg (some .cloneBound) out (size+1) source target used) =
      some (arcEnumCfg (some .cloneBound) out size source (target+1) (used+1)) := by
  simp [FinTM2.step,steinerUnaryArcEnumerationMachine,arcEnumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcEnumProgram,arcEnumNext,arcEnum_update1,arcEnum_update3,arcEnum_update4,List.replicate_succ]
  rfl

private theorem arcEnum_cloneEnd (out : List (Option Bool)) (source target used : ℕ) :
    steinerUnaryArcEnumerationMachine.step (arcEnumCfg (some .cloneBound) out 0 source target used) =
      some (arcEnumCfg (some .restoreBound) out 0 source target used) := by
  simp [FinTM2.step,steinerUnaryArcEnumerationMachine,arcEnumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcEnumProgram,arcEnumNext,arcEnum_update1]
  rfl

private def arcEnum_clone (out : List (Option Bool)) (size source target used : ℕ) :
    EvalsToInTime steinerUnaryArcEnumerationMachine.step
      (arcEnumCfg (some .cloneBound) out size source target used)
      (some (arcEnumCfg (some .restoreBound) out 0 source (target+size) (used+size))) (size+1) := by
  induction size generalizing target used with
  | zero => simpa only [Nat.add_zero] using arcEnum_one (arcEnum_cloneEnd out source target used)
  | succ size ih =>
    have first := arcEnum_one (arcEnum_cloneSymbol out size source target used)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (target+1) (used+1))
    have count (n : ℕ) : n+1+size = n+(size+1) := by omega
    simpa only [count] using all

private theorem arcEnum_restoreBoundSymbol (out : List (Option Bool)) (size source target used : ℕ) :
    steinerUnaryArcEnumerationMachine.step (arcEnumCfg (some .restoreBound) out size source target (used+1)) =
      some (arcEnumCfg (some .restoreBound) out (size+1) source target used) := by
  simp [FinTM2.step,steinerUnaryArcEnumerationMachine,arcEnumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcEnumProgram,arcEnumNext,arcEnum_update1,arcEnum_update4,List.replicate_succ]
  rfl

private theorem arcEnum_restoreBoundEnd (out : List (Option Bool)) (size source target : ℕ) :
    steinerUnaryArcEnumerationMachine.step (arcEnumCfg (some .restoreBound) out size source target 0) =
      some (arcEnumCfg (some .nextTarget) out size source target 0) := by
  simp [FinTM2.step,steinerUnaryArcEnumerationMachine,arcEnumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcEnumProgram,arcEnumNext,arcEnum_update4]
  rfl

private def arcEnum_restoreBound (out : List (Option Bool)) (size source target used : ℕ) :
    EvalsToInTime steinerUnaryArcEnumerationMachine.step
      (arcEnumCfg (some .restoreBound) out size source target used)
      (some (arcEnumCfg (some .nextTarget) out (size+used) source target 0)) (used+1) := by
  induction used generalizing size with
  | zero => simpa only [Nat.add_zero] using arcEnum_one (arcEnum_restoreBoundEnd out size source target)
  | succ used ih =>
    have first := arcEnum_one (arcEnum_restoreBoundSymbol out size source target used)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (size+1))
    have count : size+1+used = size+(used+1) := by omega
    simpa only [count] using all

private def arcEnumFieldCfg (side : ArcEnumSide) (label : ArcEnumLabel) (frame : List (Option Bool))
    (size active parked used : ℕ) : steinerUnaryArcEnumerationMachine.Cfg :=
  match side with
  | .source => arcEnumCfg (some label) frame size active parked used
  | .target => arcEnumCfg (some label) frame size parked active used

private theorem arcEnum_writeSymbol (side : ArcEnumSide) (frame : List (Option Bool)) (size active parked used : ℕ) :
    steinerUnaryArcEnumerationMachine.step (arcEnumFieldCfg side (.write side) frame size (active+1) parked used) =
      some (arcEnumFieldCfg side (.write side) (some true::frame) size active parked (used+1)) := by
  cases side <;>
    simp [FinTM2.step,steinerUnaryArcEnumerationMachine,arcEnumFieldCfg,arcEnumCfg,Turing.TM2.step,Turing.TM2.stepAux,
      arcEnumProgram,arcEnumNext,arcEnumSlot,arcEnum_update0,arcEnum_update2,arcEnum_update3,arcEnum_update4,
      List.replicate_succ] <;> rfl

private theorem arcEnum_writeEnd (side : ArcEnumSide) (frame : List (Option Bool)) (size parked used : ℕ) :
    steinerUnaryArcEnumerationMachine.step (arcEnumFieldCfg side (.write side) frame size 0 parked used) =
      some (arcEnumFieldCfg side (.restore side) frame size 0 parked used) := by
  cases side <;>
    simp [FinTM2.step,steinerUnaryArcEnumerationMachine,arcEnumFieldCfg,arcEnumCfg,Turing.TM2.step,Turing.TM2.stepAux,
      arcEnumProgram,arcEnumNext,arcEnumSlot,arcEnum_update2,arcEnum_update3] <;> rfl

private def arcEnum_write (side : ArcEnumSide) (frame : List (Option Bool)) (size active parked used : ℕ) :
    EvalsToInTime steinerUnaryArcEnumerationMachine.step
      (arcEnumFieldCfg side (.write side) frame size active parked used)
      (some (arcEnumFieldCfg side (.restore side) (enumTallies active++frame) size 0 parked (used+active))) (active+1) := by
  induction active generalizing frame used with
  | zero => simpa only [List.replicate_zero,List.nil_append,Nat.add_zero] using arcEnum_one (arcEnum_writeEnd side frame size parked used)
  | succ active ih =>
    have first := arcEnum_one (arcEnum_writeSymbol side frame size active parked used)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (some true::frame) (used+1))
    have count : used+1+active = used+(active+1) := by omega
    have prepend : enumTallies active++some true::frame = enumTallies (active+1)++frame := by
      simp only [List.replicate_add,List.replicate_one,List.append_assoc,List.singleton_append]
    simpa only [count,prepend] using all

private def arcEnumRestoredCfg (side : ArcEnumSide) (frame : List (Option Bool)) (size active parked : ℕ) :
    steinerUnaryArcEnumerationMachine.Cfg :=
  match side with
  | .source => arcEnumCfg (some .nextTarget) frame size active parked 0
  | .target => arcEnumCfg (some (.write .source)) (none::frame) size parked active 0

private theorem arcEnum_restoreSymbol (side : ArcEnumSide) (frame : List (Option Bool)) (size active parked used : ℕ) :
    steinerUnaryArcEnumerationMachine.step (arcEnumFieldCfg side (.restore side) frame size active parked (used+1)) =
      some (arcEnumFieldCfg side (.restore side) frame size (active+1) parked used) := by
  cases side <;>
    simp [FinTM2.step,steinerUnaryArcEnumerationMachine,arcEnumFieldCfg,arcEnumCfg,Turing.TM2.step,Turing.TM2.stepAux,
      arcEnumProgram,arcEnumNext,arcEnumSlot,arcEnum_update2,arcEnum_update3,arcEnum_update4,List.replicate_succ] <;> rfl

private theorem arcEnum_restoreEnd (side : ArcEnumSide) (frame : List (Option Bool)) (size active parked : ℕ) :
    steinerUnaryArcEnumerationMachine.step (arcEnumFieldCfg side (.restore side) frame size active parked 0) =
      some (arcEnumRestoredCfg side frame size active parked) := by
  cases side <;>
    simp [FinTM2.step,steinerUnaryArcEnumerationMachine,arcEnumFieldCfg,arcEnumCfg,Turing.TM2.step,Turing.TM2.stepAux,
      arcEnumProgram,arcEnumNext,arcEnumAfterRestore,arcEnumRestoredCfg,arcEnum_update0,arcEnum_update4] <;> rfl

private def arcEnum_restore (side : ArcEnumSide) (frame : List (Option Bool)) (size active parked used : ℕ) :
    EvalsToInTime steinerUnaryArcEnumerationMachine.step
      (arcEnumFieldCfg side (.restore side) frame size active parked used)
      (some (arcEnumRestoredCfg side frame size (active+used) parked)) (used+1) := by
  induction used generalizing active with
  | zero => simpa only [Nat.add_zero] using arcEnum_one (arcEnum_restoreEnd side frame size active parked)
  | succ used ih =>
    have first := arcEnum_one (arcEnum_restoreSymbol side frame size active parked used)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (active+1))
    have count : active+1+used = active+(used+1) := by omega
    simpa only [count] using all

private theorem arcEnum_startTarget (out : List (Option Bool)) (size source target : ℕ) :
    steinerUnaryArcEnumerationMachine.step (arcEnumCfg (some .nextTarget) out size source (target+1) 0) =
      some (arcEnumCfg (some (.write .target)) (none::out) size source target 0) := by
  simp [FinTM2.step,steinerUnaryArcEnumerationMachine,arcEnumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcEnumProgram,arcEnumNext,arcEnum_update0,arcEnum_update3,List.replicate_succ]
  rfl

private theorem arcEnum_endTargets (out : List (Option Bool)) (size source : ℕ) :
    steinerUnaryArcEnumerationMachine.step (arcEnumCfg (some .nextTarget) out size source 0 0) =
      some (arcEnumCfg (some .nextSource) out size source 0 0) := by
  simp [FinTM2.step,steinerUnaryArcEnumerationMachine,arcEnumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcEnumProgram,arcEnumNext,arcEnum_update3]
  rfl

private def arcEnum_pair (out : List (Option Bool)) (size source target : ℕ) :
    EvalsToInTime steinerUnaryArcEnumerationMachine.step
      (arcEnumCfg (some .nextTarget) out size source (target+1) 0)
      (some (arcEnumCfg (some .nextTarget) (encodeSteinerUnaryArcRows [(source,target)]++out) size source target 0))
      (2*source+2*target+5) := by
  let last := enumTallies target++none::out
  let first := enumTallies source++none::last
  have start := arcEnum_one (arcEnum_startTarget out size source target)
  have targetWritten := arcEnum_write .target (none::out) size target source 0
  have targetRestored := arcEnum_restore .target last size 0 source target
  rw [Nat.zero_add] at targetWritten targetRestored
  have sourceWritten := arcEnum_write .source (none::last) size source target 0
  have sourceRestored := arcEnum_restore .source first size 0 target source
  rw [Nat.zero_add] at sourceWritten sourceRestored
  have a := EvalsToInTime.trans _ _ _ _ _ _ start targetWritten
  have b := EvalsToInTime.trans _ _ _ _ _ _ a targetRestored
  have c := EvalsToInTime.trans _ _ _ _ _ _ b sourceWritten
  have all := EvalsToInTime.trans _ _ _ _ _ _ c sourceRestored
  have exactFrame : first = encodeSteinerUnaryArcRows [(source,target)]++out := by
    rw [encodeSteinerUnaryArcRows_cons]
    change first = (enumTallies source++none::(enumTallies target++[none]))++out
    simp only [first,last,List.append_assoc,List.cons_append,List.nil_append]
  change EvalsToInTime steinerUnaryArcEnumerationMachine.step _ (some (arcEnumCfg (some .nextTarget) first size source target 0)) _ at all
  rw [exactFrame] at all
  exact ⟨all.toEvalsTo,by have paid := all.steps_le_m; omega⟩

private def arcEnumTargetRows (source targets : ℕ) : List (ℕ × ℕ) := (List.range targets).map fun target => (source,target)

private theorem arcEnumTargetRows_succ (source targets : ℕ) :
    arcEnumTargetRows source (targets+1) = arcEnumTargetRows source targets++[(source,targets)] := by
  simp only [arcEnumTargetRows,List.range_succ,List.map_append,List.map_cons,List.map_nil]

private def arcEnum_targets (out : List (Option Bool)) (size source targets : ℕ) :
    EvalsToInTime steinerUnaryArcEnumerationMachine.step
      (arcEnumCfg (some .nextTarget) out size source targets 0)
      (some (arcEnumCfg (some .nextSource) (encodeSteinerUnaryArcRows (arcEnumTargetRows source targets)++out)
        size source 0 0)) (targets^2+(2*source+4)*targets+1) := by
  induction targets generalizing out with
  | zero =>
    have empty : encodeSteinerUnaryArcRows (arcEnumTargetRows source 0) = [] := rfl
    simpa only [empty,List.nil_append,pow_two,Nat.zero_mul,Nat.mul_zero,Nat.zero_add]
      using arcEnum_one (arcEnum_endTargets out size source)
  | succ targets ih =>
    have row := arcEnum_pair out size source targets
    have all := EvalsToInTime.trans _ _ _ _ _ _ row (ih (encodeSteinerUnaryArcRows [(source,targets)]++out))
    rw [arcEnumTargetRows_succ,encodeSteinerUnaryArcRows_append,List.append_assoc]
    exact ⟨all.toEvalsTo,by have paid := all.steps_le_m; nlinarith only [paid]⟩

private def arcEnumPairs (sources targets : ℕ) : List (ℕ × ℕ) := (List.range sources).product (List.range targets)

private theorem arcEnumPairs_succ (sources targets : ℕ) :
    arcEnumPairs (sources+1) targets = arcEnumPairs sources targets++arcEnumTargetRows sources targets := by
  unfold arcEnumPairs arcEnumTargetRows
  rw [List.range_succ]
  simp only [List.product,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

private def arcEnum_sources (out : List (Option Bool)) (size sources : ℕ) :
    EvalsToInTime steinerUnaryArcEnumerationMachine.step
      (arcEnumCfg (some .nextSource) out size sources 0 0)
      (some (arcEnumCfg (some .clearBound) (encodeSteinerUnaryArcRows (arcEnumPairs sources size)++out)
        size 0 0 0)) (sources*size^2+size*sources^2+5*size*sources+4*sources+1) := by
  induction sources generalizing out with
  | zero =>
    have empty : encodeSteinerUnaryArcRows (arcEnumPairs 0 size) = [] := rfl
    simpa only [empty,List.nil_append,pow_two,Nat.zero_mul,Nat.mul_zero,Nat.zero_add]
      using arcEnum_one (arcEnum_endSources out size)
  | succ sources ih =>
    have start := arcEnum_one (arcEnum_startSource out size sources)
    have cloned := arcEnum_clone out size sources 0 0
    have restored := arcEnum_restoreBound out 0 sources size size
    rw [Nat.zero_add] at cloned restored
    have prepared := EvalsToInTime.trans _ _ _ _ _ _ (EvalsToInTime.trans _ _ _ _ _ _ start cloned) restored
    have row := EvalsToInTime.trans _ _ _ _ _ _ prepared (arcEnum_targets out size sources size)
    have all := EvalsToInTime.trans _ _ _ _ _ _ row (ih (encodeSteinerUnaryArcRows (arcEnumTargetRows sources size)++out))
    rw [arcEnumPairs_succ,encodeSteinerUnaryArcRows_append,List.append_assoc]
    exact ⟨all.toEvalsTo,by have paid := all.steps_le_m; nlinarith only [paid]⟩

private theorem arcEnum_clearSymbol (out : List (Option Bool)) (size : ℕ) :
    steinerUnaryArcEnumerationMachine.step (arcEnumCfg (some .clearBound) out (size+1) 0 0 0) =
      some (arcEnumCfg (some .clearBound) out size 0 0 0) := by
  simp [FinTM2.step,steinerUnaryArcEnumerationMachine,arcEnumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcEnumProgram,arcEnumNext,arcEnum_update1,List.replicate_succ]
  rfl

private theorem arcEnum_clearEnd (out : List (Option Bool)) :
    steinerUnaryArcEnumerationMachine.step (arcEnumCfg (some .clearBound) out 0 0 0 0) =
      some (arcEnumCfg none out 0 0 0 0) := by
  simp [FinTM2.step,steinerUnaryArcEnumerationMachine,arcEnumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcEnumProgram,arcEnum_update1]
  rfl

private def arcEnum_clear (out : List (Option Bool)) (size : ℕ) :
    EvalsToInTime steinerUnaryArcEnumerationMachine.step (arcEnumCfg (some .clearBound) out size 0 0 0)
      (some (arcEnumCfg none out 0 0 0 0)) (size+1) := by
  induction size with
  | zero => exact arcEnum_one (arcEnum_clearEnd out)
  | succ size ih => exact EvalsToInTime.trans _ _ _ _ _ _ (arcEnum_one (arcEnum_clearSymbol out size)) ih

private theorem arcEnum_indexList (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi _
    simp [List.getElem_range]

private theorem arcEnumPairs_values (n : ℕ) : arcEnumPairs n n = (steinerAllArcQueries n).map steinerUnaryArcValues := by
  unfold steinerAllArcQueries arcEnumPairs
  rw [← arcEnum_indexList n]
  simp only [List.product,List.map_flatMap,List.flatMap_map,List.map_map]
  rfl

/-- On a unary vertex count the machine generates the complete query frame. -/
def encodeSteinerUnaryArcEnumerationInput (n : ℕ) : List (Option Bool) := List.replicate n (some true)

/-- The result uses precisely the order and endpoint frames of the
finite all-pairs cardinality query. -/
def steinerUnaryArcEnumerationAnswer (n : ℕ) : List (Option Bool) :=
  encodeSteinerUnaryArcRows ((steinerAllArcQueries n).map steinerUnaryArcValues)

private theorem arcEnum_init (frame : List (Option Bool)) :
    initList steinerUnaryArcEnumerationMachine frame = arcEnumCfg (some .loadBound) frame 0 0 0 0 := by
  apply congrArg (fun stk : Fin 5 → List (Option Bool) => (⟨some .loadBound,none,stk⟩ : steinerUnaryArcEnumerationMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem arcEnum_halt (frame : List (Option Bool)) :
    haltList steinerUnaryArcEnumerationMachine frame = arcEnumCfg none frame 0 0 0 0 := by
  apply congrArg (fun stk : Fin 5 → List (Option Bool) => (⟨none,none,stk⟩ : steinerUnaryArcEnumerationMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- Generate the entire all-pairs frame in at most the stated cubic
number of machine transitions, including zero vertices. -/
def steinerUnaryArcEnumerationMachine_run (n : ℕ) :
    TM2OutputsInTime steinerUnaryArcEnumerationMachine (encodeSteinerUnaryArcEnumerationInput n)
      (some (steinerUnaryArcEnumerationAnswer n)) (2*n^3+5*n^2+6*n+3) := by
  let out := encodeSteinerUnaryArcRows (arcEnumPairs n n)
  have read := arcEnum_load n 0 0
  rw [Nat.zero_add] at read
  have listed := arcEnum_sources [] n n
  rw [List.append_nil] at listed
  have prepared := EvalsToInTime.trans _ _ _ _ _ _ read listed
  have all := EvalsToInTime.trans _ _ _ _ _ _ prepared (arcEnum_clear out n)
  change EvalsToInTime steinerUnaryArcEnumerationMachine.step _ (some (haltList steinerUnaryArcEnumerationMachine _)) _
  rw [arcEnum_init,arcEnum_halt,steinerUnaryArcEnumerationAnswer,← arcEnumPairs_values]
  exact ⟨all.toEvalsTo,by have paid := all.steps_le_m; nlinarith only [paid]⟩

/-- The time polynomial is measured in the length of the unary count. -/
noncomputable def steinerUnaryArcEnumerationMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryArcEnumerationInput id steinerUnaryArcEnumerationAnswer where
  tm := steinerUnaryArcEnumerationMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2*Polynomial.X^3+Polynomial.C 5*Polynomial.X^2+Polynomial.C 6*Polynomial.X+Polynomial.C 3
  outputsFun n := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,
      Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_pow,encodeSteinerUnaryArcEnumerationInput,
      List.length_replicate] using steinerUnaryArcEnumerationMachine_run n

private theorem arcEnum_single_length (source target : ℕ) :
    (encodeSteinerUnaryArcRows [(source,target)]).length = source+target+2 := by
  rw [encodeSteinerUnaryArcRows_cons]
  simp only [List.length_append,List.length_replicate,List.length_cons,show encodeSteinerUnaryArcRows [] = [] from rfl,
    List.length_nil]
  omega

private theorem arcEnum_target_length (source targets : ℕ) :
    2*(encodeSteinerUnaryArcRows (arcEnumTargetRows source targets)).length = targets^2+(2*source+3)*targets := by
  induction targets with
  | zero =>
    have empty : encodeSteinerUnaryArcRows (arcEnumTargetRows source 0) = [] := rfl
    simp [empty]
  | succ targets ih =>
    rw [arcEnumTargetRows_succ,encodeSteinerUnaryArcRows_append,List.length_append,Nat.mul_add,ih,arcEnum_single_length]
    ring

private theorem arcEnum_pairs_length (sources targets : ℕ) :
    2*(encodeSteinerUnaryArcRows (arcEnumPairs sources targets)).length =
      sources*targets^2+targets*sources^2+2*targets*sources := by
  induction sources with
  | zero =>
    have empty : encodeSteinerUnaryArcRows (arcEnumPairs 0 targets) = [] := rfl
    simp [empty]
  | succ sources ih =>
    rw [arcEnumPairs_succ,encodeSteinerUnaryArcRows_append,List.length_append,Nat.mul_add,ih,arcEnum_target_length]
    ring

/-- The output contains all unary endpoint tallies and two delimiters
per ordered candidate pair. -/
theorem steinerUnaryArcEnumerationAnswer_length (n : ℕ) :
    (steinerUnaryArcEnumerationAnswer n).length = n^3+n^2 := by
  have count := arcEnum_pairs_length n n
  rw [arcEnumPairs_values] at count
  change 2*(steinerUnaryArcEnumerationAnswer n).length = _ at count
  nlinarith only [count]

end OnlineReachabilityPreservers
