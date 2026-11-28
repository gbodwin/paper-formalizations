import OnlineReachabilityPreservers.SteinerEndpointUnaryBatchMachine

/-! Test membership of one unary arc in an ordered list of unary arc rows. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private inductive UnaryArcSide where
  | first
  | second
  deriving DecidableEq

private instance : Fintype UnaryArcSide where
  elems := {.first,.second}
  complete := by intro side; cases side <;> simp

private inductive UnaryArcLabel where
  | loadQuery (side : UnaryArcSide)
  | nextRow
  | scan (side : UnaryArcSide)
  | restore (side : UnaryArcSide)
  | clear (side : UnaryArcSide)
  deriving Fintype

private structure UnaryArcRegister where
  seen : Option (Option Bool)
  equalSoFar : Bool
  firstEqual : Bool
  found : Bool
  deriving Fintype

private def unaryArcState (found : Bool) (equalSoFar firstEqual : Bool := true) : UnaryArcRegister :=
  ⟨none,equalSoFar,firstEqual,found⟩

private abbrev UnaryArcProgram :=
  StackMachineTag.Program (Fin 4) (Option Bool) UnaryArcLabel UnaryArcRegister

private def unaryArcObserve (r : UnaryArcRegister) (seen : Option (Option Bool)) : UnaryArcRegister :=
  {r with seen}

private def unaryArcNext (label : UnaryArcLabel) : UnaryArcProgram :=
  load (fun r => {r with seen := none}) (goto (fun _ => label))

private def unaryArcSlot : UnaryArcSide → Fin 4
  | .first => 1
  | .second => 2

private def unaryArcAfterQuery : UnaryArcSide → UnaryArcLabel
  | .first => .loadQuery .second
  | .second => .nextRow

private def unaryArcAfterRestore : UnaryArcSide → UnaryArcProgram
  | .first => load (fun r => unaryArcState r.found true r.equalSoFar) (goto (fun _ => .scan .second))
  | .second => load (fun r => unaryArcState (r.found || (r.firstEqual && r.equalSoFar))) (goto (fun _ => .nextRow))

private def unaryArcAfterClear : UnaryArcSide → UnaryArcProgram
  | .first => unaryArcNext (.clear .second)
  | .second => push 0 (fun r => some r.found) (load (fun _ => unaryArcState false) halt)

private def unaryArcProgram : UnaryArcLabel → UnaryArcProgram
  | .loadQuery side =>
    pop 0 unaryArcObserve <|
      branch (fun r => r.seen.join.isSome)
        (push (unaryArcSlot side) (fun _ => some true) (unaryArcNext (.loadQuery side)))
        (unaryArcNext (unaryArcAfterQuery side))
  | .nextRow =>
    peek 0 unaryArcObserve <|
      branch (fun r => r.seen.isSome)
        (unaryArcNext (.scan .first))
        (unaryArcNext (.clear .first))
  | .scan side =>
    pop 0 unaryArcObserve <|
      branch (fun r => r.seen.join.isSome)
        (pop (unaryArcSlot side) unaryArcObserve <|
          branch (fun r => r.seen.isSome)
            (push 3 (fun _ => some true) (unaryArcNext (.scan side)))
            (load (fun r => {r with seen := none,equalSoFar := false}) (goto (fun _ => .scan side))))
        (peek (unaryArcSlot side) unaryArcObserve <|
          load (fun r => {r with seen := none,equalSoFar := r.equalSoFar && r.seen.isNone}) (goto (fun _ => .restore side)))
  | .restore side =>
    pop 3 unaryArcObserve <|
      branch (fun r => r.seen.isSome)
        (push (unaryArcSlot side) (fun _ => some true) (unaryArcNext (.restore side)))
        (unaryArcAfterRestore side)
  | .clear side =>
    pop (unaryArcSlot side) unaryArcObserve <|
      branch (fun r => r.seen.isSome)
        (unaryArcNext (.clear side))
        (unaryArcAfterClear side)

/-- Load the two unary query endpoints. Compare each field of the
row stream with its corresponding query stack and restore the query
between comparisons. The output records whether any row matched. -/
abbrev steinerUnaryArcQueryMachine : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 0
  Γ _ := Option Bool
  Λ := UnaryArcLabel
  main := .loadQuery .first
  σ := UnaryArcRegister
  initialState := unaryArcState false
  m := unaryArcProgram

private abbrev arcTallies (n : ℕ) : List (Option Bool) := List.replicate n (some true)

private def unaryArcCfg (label : Option UnaryArcLabel) (r : UnaryArcRegister)
    (input : List (Option Bool)) (first second used : ℕ) : steinerUnaryArcQueryMachine.Cfg where
  l := label
  var := r
  stk := ![input,arcTallies first,arcTallies second,arcTallies used]

private def unaryArcFieldCfg (side : UnaryArcSide) (label : UnaryArcLabel) (r : UnaryArcRegister)
    (input : List (Option Bool)) (counter parked used : ℕ) : steinerUnaryArcQueryMachine.Cfg :=
  match side with
  | .first => unaryArcCfg (some label) r input counter parked used
  | .second => unaryArcCfg (some label) r input parked counter used

private theorem unaryArc_update0 (w a b t next : List (Option Bool)) :
    Function.update (![w,a,b,t] : Fin 4 → List (Option Bool)) 0 next = ![next,a,b,t] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem unaryArc_update1 (w a b t next : List (Option Bool)) :
    Function.update (![w,a,b,t] : Fin 4 → List (Option Bool)) 1 next = ![w,next,b,t] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem unaryArc_update2 (w a b t next : List (Option Bool)) :
    Function.update (![w,a,b,t] : Fin 4 → List (Option Bool)) 2 next = ![w,a,next,t] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem unaryArc_update3 (w a b t next : List (Option Bool)) :
    Function.update (![w,a,b,t] : Fin 4 → List (Option Bool)) 3 next = ![w,a,b,next] := by
  funext i
  fin_cases i <;> simp [Function.update]

private def unaryArc_one {a b : steinerUnaryArcQueryMachine.Cfg} (step : steinerUnaryArcQueryMachine.step a = some b) :
    EvalsToInTime steinerUnaryArcQueryMachine.step a (some b) 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := step

private theorem unaryArc_loadTally (side : UnaryArcSide) (counter parked : ℕ) (input : List (Option Bool)) :
    steinerUnaryArcQueryMachine.step
      (unaryArcFieldCfg side (.loadQuery side) (unaryArcState false) (some true::input) counter parked 0) =
    some (unaryArcFieldCfg side (.loadQuery side) (unaryArcState false) input (counter+1) parked 0) := by
  cases side <;>
    simp [FinTM2.step,steinerUnaryArcQueryMachine,unaryArcCfg,unaryArcFieldCfg,Turing.TM2.step,Turing.TM2.stepAux,
      unaryArcProgram,unaryArcObserve,unaryArcNext,unaryArcSlot,unaryArc_update0,unaryArc_update1,unaryArc_update2,
      List.replicate_succ,unaryArcState] <;> rfl

private theorem unaryArc_loadDivider (side : UnaryArcSide) (counter parked : ℕ) (input : List (Option Bool)) :
    steinerUnaryArcQueryMachine.step
      (unaryArcFieldCfg side (.loadQuery side) (unaryArcState false) (none::input) counter parked 0) =
    some (unaryArcFieldCfg side (unaryArcAfterQuery side) (unaryArcState false) input counter parked 0) := by
  cases side <;>
    simp [FinTM2.step,steinerUnaryArcQueryMachine,unaryArcCfg,unaryArcFieldCfg,Turing.TM2.step,Turing.TM2.stepAux,
      unaryArcProgram,unaryArcObserve,unaryArcNext,unaryArcSlot,unaryArcAfterQuery,unaryArc_update0,unaryArcState] <;> rfl

private def unaryArc_load (side : UnaryArcSide) (remaining counter parked : ℕ) (input : List (Option Bool)) :
    EvalsToInTime steinerUnaryArcQueryMachine.step
      (unaryArcFieldCfg side (.loadQuery side) (unaryArcState false) (arcTallies remaining++none::input) counter parked 0)
      (some (unaryArcFieldCfg side (unaryArcAfterQuery side) (unaryArcState false) input (counter+remaining) parked 0))
      (remaining+1) := by
  induction remaining generalizing counter with
  | zero => simpa only [Nat.add_zero,List.replicate_zero,List.nil_append] using
      unaryArc_one (unaryArc_loadDivider side counter parked input)
  | succ remaining ih =>
    have first := unaryArc_one (unaryArc_loadTally side counter parked (arcTallies remaining++none::input))
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (counter+1))
    have count : counter+1+remaining = counter+(remaining+1) := by omega
    simpa only [List.replicate_succ,List.cons_append,count] using all

private theorem unaryArc_nextRow (symbol : Option Bool) (input : List (Option Bool)) (first second : ℕ) (found : Bool) :
    steinerUnaryArcQueryMachine.step (unaryArcCfg (some .nextRow) (unaryArcState found) (symbol::input) first second 0) =
      some (unaryArcCfg (some (.scan .first)) (unaryArcState found) (symbol::input) first second 0) := by
  simp [FinTM2.step,steinerUnaryArcQueryMachine,unaryArcCfg,Turing.TM2.step,Turing.TM2.stepAux,unaryArcProgram,
    unaryArcObserve,unaryArcNext,unaryArcState]
  rfl

private theorem unaryArc_endRows (first second : ℕ) (found : Bool) :
    steinerUnaryArcQueryMachine.step (unaryArcCfg (some .nextRow) (unaryArcState found) [] first second 0) =
      some (unaryArcCfg (some (.clear .first)) (unaryArcState found) [] first second 0) := by
  simp [FinTM2.step,steinerUnaryArcQueryMachine,unaryArcCfg,Turing.TM2.step,Turing.TM2.stepAux,unaryArcProgram,
    unaryArcObserve,unaryArcNext,unaryArcState]
  rfl

private theorem unaryArc_scanMatch (side : UnaryArcSide) (counter parked used : ℕ) (input : List (Option Bool))
    (found equalSoFar firstEqual : Bool) :
    steinerUnaryArcQueryMachine.step
      (unaryArcFieldCfg side (.scan side) (unaryArcState found equalSoFar firstEqual) (some true::input)
        (counter+1) parked used) = some
      (unaryArcFieldCfg side (.scan side) (unaryArcState found equalSoFar firstEqual) input counter parked (used+1)) := by
  cases side <;>
    simp [FinTM2.step,steinerUnaryArcQueryMachine,unaryArcCfg,unaryArcFieldCfg,Turing.TM2.step,Turing.TM2.stepAux,
      unaryArcProgram,unaryArcObserve,unaryArcNext,unaryArcSlot,unaryArc_update0,unaryArc_update1,unaryArc_update2,
      unaryArc_update3,List.replicate_succ,unaryArcState] <;> rfl

private theorem unaryArc_scanExcess (side : UnaryArcSide) (parked used : ℕ) (input : List (Option Bool))
    (found equalSoFar firstEqual : Bool) :
    steinerUnaryArcQueryMachine.step
      (unaryArcFieldCfg side (.scan side) (unaryArcState found equalSoFar firstEqual) (some true::input) 0 parked used) =
    some (unaryArcFieldCfg side (.scan side) (unaryArcState found false firstEqual) input 0 parked used) := by
  cases side <;>
    simp [FinTM2.step,steinerUnaryArcQueryMachine,unaryArcCfg,unaryArcFieldCfg,Turing.TM2.step,Turing.TM2.stepAux,
      unaryArcProgram,unaryArcObserve,unaryArcNext,unaryArcSlot,unaryArc_update0,unaryArc_update1,unaryArc_update2,
      unaryArcState] <;> rfl

private theorem unaryArc_scanDivider (side : UnaryArcSide) (counter parked used : ℕ) (input : List (Option Bool))
    (found equalSoFar firstEqual : Bool) :
    steinerUnaryArcQueryMachine.step
      (unaryArcFieldCfg side (.scan side) (unaryArcState found equalSoFar firstEqual) (none::input) counter parked used) =
    some (unaryArcFieldCfg side (.restore side) (unaryArcState found (equalSoFar && decide (counter = 0)) firstEqual)
      input counter parked used) := by
  cases side <;> cases counter <;>
    simp [FinTM2.step,steinerUnaryArcQueryMachine,unaryArcCfg,unaryArcFieldCfg,Turing.TM2.step,Turing.TM2.stepAux,
      unaryArcProgram,unaryArcObserve,unaryArcSlot,unaryArc_update0,List.replicate_succ,unaryArcState] <;> rfl

private def unaryArc_scan (side : UnaryArcSide) (remaining counter parked used : ℕ) (input : List (Option Bool))
    (found equalSoFar firstEqual : Bool) :
    EvalsToInTime steinerUnaryArcQueryMachine.step
      (unaryArcFieldCfg side (.scan side) (unaryArcState found equalSoFar firstEqual)
        (arcTallies remaining++none::input) counter parked used)
      (some (unaryArcFieldCfg side (.restore side) (unaryArcState found (equalSoFar && decide (remaining = counter)) firstEqual)
        input (counter-remaining) parked (used+min remaining counter))) (remaining+1) := by
  induction remaining generalizing counter used equalSoFar with
  | zero =>
    simpa only [List.replicate_zero,List.nil_append,Nat.sub_zero,Nat.zero_min,Nat.add_zero,eq_comm]
      using unaryArc_one (unaryArc_scanDivider side counter parked used input found equalSoFar firstEqual)
  | succ remaining ih =>
    cases counter with
    | zero =>
      have first := unaryArc_one (unaryArc_scanExcess side parked used (arcTallies remaining++none::input)
        found equalSoFar firstEqual)
      have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih 0 used false)
      simpa only [List.replicate_succ,List.cons_append,Nat.zero_sub,Nat.min_zero,Nat.add_zero,
        Nat.succ_ne_zero,decide_false,Bool.and_false,Bool.false_and] using all
    | succ counter =>
      have first := unaryArc_one (unaryArc_scanMatch side counter parked used (arcTallies remaining++none::input)
        found equalSoFar firstEqual)
      have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih counter (used+1) equalSoFar)
      have moved : used+1+min remaining counter = used+(min remaining counter).succ := by omega
      simpa only [List.replicate_succ,List.cons_append,Nat.succ_sub_succ_eq_sub,Nat.succ_min_succ,
        Nat.succ.injEq,moved] using all

private def unaryArcAfterCompare (side : UnaryArcSide) (found equalSoFar firstEqual : Bool)
    (input : List (Option Bool)) (counter parked : ℕ) : steinerUnaryArcQueryMachine.Cfg :=
  match side with
  | .first => unaryArcCfg (some (.scan .second)) (unaryArcState found true equalSoFar) input counter parked 0
  | .second => unaryArcCfg (some .nextRow) (unaryArcState (found || (firstEqual && equalSoFar))) input parked counter 0

private theorem unaryArc_restoreTally (side : UnaryArcSide) (counter parked used : ℕ) (input : List (Option Bool))
    (found equalSoFar firstEqual : Bool) :
    steinerUnaryArcQueryMachine.step
      (unaryArcFieldCfg side (.restore side) (unaryArcState found equalSoFar firstEqual) input counter parked (used+1)) =
    some (unaryArcFieldCfg side (.restore side) (unaryArcState found equalSoFar firstEqual) input (counter+1) parked used) := by
  cases side <;>
    simp [FinTM2.step,steinerUnaryArcQueryMachine,unaryArcCfg,unaryArcFieldCfg,Turing.TM2.step,Turing.TM2.stepAux,
      unaryArcProgram,unaryArcObserve,unaryArcNext,unaryArcSlot,unaryArc_update1,unaryArc_update2,unaryArc_update3,
      List.replicate_succ,unaryArcState] <;> rfl

private theorem unaryArc_restoreEnd (side : UnaryArcSide) (counter parked : ℕ) (input : List (Option Bool))
    (found equalSoFar firstEqual : Bool) :
    steinerUnaryArcQueryMachine.step
      (unaryArcFieldCfg side (.restore side) (unaryArcState found equalSoFar firstEqual) input counter parked 0) =
    some (unaryArcAfterCompare side found equalSoFar firstEqual input counter parked) := by
  cases side <;>
    simp [FinTM2.step,steinerUnaryArcQueryMachine,unaryArcCfg,unaryArcFieldCfg,Turing.TM2.step,Turing.TM2.stepAux,
      unaryArcProgram,unaryArcObserve,unaryArcAfterRestore,unaryArcAfterCompare,unaryArc_update3,unaryArcState] <;> rfl

private def unaryArc_restore (side : UnaryArcSide) (counter parked used : ℕ) (input : List (Option Bool))
    (found equalSoFar firstEqual : Bool) :
    EvalsToInTime steinerUnaryArcQueryMachine.step
      (unaryArcFieldCfg side (.restore side) (unaryArcState found equalSoFar firstEqual) input counter parked used)
      (some (unaryArcAfterCompare side found equalSoFar firstEqual input (counter+used) parked)) (used+1) := by
  induction used generalizing counter with
  | zero => simpa only [Nat.add_zero] using unaryArc_one (unaryArc_restoreEnd side counter parked input found equalSoFar firstEqual)
  | succ used ih =>
    have first := unaryArc_one (unaryArc_restoreTally side counter parked used input found equalSoFar firstEqual)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (counter+1))
    have count : counter+1+used = counter+(used+1) := by omega
    simpa only [count] using all

private def unaryArc_compare (side : UnaryArcSide) (field query parked : ℕ) (input : List (Option Bool))
    (found firstEqual : Bool) :
    EvalsToInTime steinerUnaryArcQueryMachine.step
      (unaryArcFieldCfg side (.scan side) (unaryArcState found true firstEqual)
        (arcTallies field++none::input) query parked 0)
      (some (unaryArcAfterCompare side found (decide (field = query)) firstEqual input query parked))
      (2*field+2) := by
  have scanned := unaryArc_scan side field query parked 0 input found true firstEqual
  simp only [Bool.true_and,Nat.zero_add] at scanned
  have backed := unaryArc_restore side (query-field) parked (min field query) input found (decide (field = query)) firstEqual
  have returns : query-field+min field query = query := by omega
  rw [returns] at backed
  have all := EvalsToInTime.trans _ _ _ _ _ _ scanned backed
  exact ⟨all.toEvalsTo,by
    have paid := all.steps_le_m
    have atMost := min_le_left field query
    omega⟩

private def unaryArcAfterClearCfg (side : UnaryArcSide) (parked : ℕ) (found : Bool) : steinerUnaryArcQueryMachine.Cfg :=
  match side with
  | .first => unaryArcCfg (some (.clear .second)) (unaryArcState found) [] 0 parked 0
  | .second => unaryArcCfg none (unaryArcState false) [some found] parked 0 0

private theorem unaryArc_clearTally (side : UnaryArcSide) (counter parked : ℕ) (found : Bool) :
    steinerUnaryArcQueryMachine.step (unaryArcFieldCfg side (.clear side) (unaryArcState found) [] (counter+1) parked 0) =
      some (unaryArcFieldCfg side (.clear side) (unaryArcState found) [] counter parked 0) := by
  cases side <;>
    simp [FinTM2.step,steinerUnaryArcQueryMachine,unaryArcCfg,unaryArcFieldCfg,Turing.TM2.step,Turing.TM2.stepAux,
      unaryArcProgram,unaryArcObserve,unaryArcNext,unaryArcSlot,unaryArc_update1,unaryArc_update2,
      List.replicate_succ,unaryArcState] <;> rfl

private theorem unaryArc_clearEnd (side : UnaryArcSide) (parked : ℕ) (found : Bool) :
    steinerUnaryArcQueryMachine.step (unaryArcFieldCfg side (.clear side) (unaryArcState found) [] 0 parked 0) =
      some (unaryArcAfterClearCfg side parked found) := by
  cases side <;>
    simp [FinTM2.step,steinerUnaryArcQueryMachine,unaryArcCfg,unaryArcFieldCfg,Turing.TM2.step,Turing.TM2.stepAux,
      unaryArcProgram,unaryArcObserve,unaryArcNext,unaryArcSlot,unaryArcAfterClear,unaryArcAfterClearCfg,
      unaryArc_update0,unaryArc_update1,unaryArc_update2,unaryArcState] <;> rfl

private def unaryArc_clear (side : UnaryArcSide) (counter parked : ℕ) (found : Bool) :
    EvalsToInTime steinerUnaryArcQueryMachine.step
      (unaryArcFieldCfg side (.clear side) (unaryArcState found) [] counter parked 0)
      (some (unaryArcAfterClearCfg side parked found)) (counter+1) := by
  induction counter with
  | zero => exact unaryArc_one (unaryArc_clearEnd side parked found)
  | succ counter ih =>
    exact EvalsToInTime.trans _ _ _ _ _ _ (unaryArc_one (unaryArc_clearTally side counter parked found)) ih

/-- Use the unary endpoint frames for pairs of consecutive arc endpoints. -/
def encodeSteinerUnaryArcRows (arcs : List (ℕ × ℕ)) : List (Option Bool) :=
  encodeSteinerUnaryEndpointValues (arcs.flatMap fun arc => [arc.1,arc.2])

/-- Each row consists of two unary fields with separate delimiters. -/
theorem encodeSteinerUnaryArcRows_cons (a b : ℕ) (rows : List (ℕ × ℕ)) :
    encodeSteinerUnaryArcRows ((a,b)::rows) =
      List.replicate a (some true)++none::(List.replicate b (some true)++none::encodeSteinerUnaryArcRows rows) := by
  simp only [encodeSteinerUnaryArcRows,List.flatMap_cons,encodeSteinerUnaryEndpointValues,
    List.flatMap_append,List.flatMap_nil,List.append_nil]
  change ((((encodeSteinerUnaryProductCount a).map some++[none])++
    ((encodeSteinerUnaryProductCount b).map some++[none]))++encodeSteinerUnaryArcRows rows) = _
  simp only [encodeSteinerUnaryArcRows,encodeSteinerUnaryEndpointValues,encodeSteinerUnaryProductCount,
    List.map_replicate,List.append_assoc,List.cons_append,List.nil_append]

theorem encodeSteinerUnaryArcRows_append (first second : List (ℕ × ℕ)) :
    encodeSteinerUnaryArcRows (first++second) = encodeSteinerUnaryArcRows first++encodeSteinerUnaryArcRows second := by
  simp only [encodeSteinerUnaryArcRows,encodeSteinerUnaryEndpointValues,List.flatMap_append]

private theorem unaryArc_row_match (q₁ q₂ a b : ℕ) :
    (decide (a = q₁) && decide (b = q₂)) = decide ((q₁,q₂) = (a,b)) := by
  simp only [Prod.mk.injEq,Bool.decide_and,eq_comm]

private def unaryArc_row (q₁ q₂ a b : ℕ) (input : List (Option Bool)) (found : Bool) :
    EvalsToInTime steinerUnaryArcQueryMachine.step
      (unaryArcCfg (some .nextRow) (unaryArcState found) (arcTallies a++none::(arcTallies b++none::input)) q₁ q₂ 0)
      (some (unaryArcCfg (some .nextRow) (unaryArcState (found || decide ((q₁,q₂) = (a,b)))) input q₁ q₂ 0))
      (2*a+2*b+5) := by
  let framed := arcTallies a++none::(arcTallies b++none::input)
  have start : steinerUnaryArcQueryMachine.step (unaryArcCfg (some .nextRow) (unaryArcState found) framed q₁ q₂ 0) =
      some (unaryArcCfg (some (.scan .first)) (unaryArcState found) framed q₁ q₂ 0) := by
    cases a with
    | zero => exact unaryArc_nextRow _ _ q₁ q₂ found
    | succ a =>
      simpa only [framed,List.replicate_succ,List.cons_append] using
        unaryArc_nextRow (some true) (arcTallies a++none::(arcTallies b++none::input)) q₁ q₂ found
  have left := unaryArc_compare .first a q₁ q₂ (arcTallies b++none::input) found true
  have right := unaryArc_compare .second b q₂ q₁ input found (decide (a = q₁))
  have first := EvalsToInTime.trans _ _ _ _ _ _ (unaryArc_one start) left
  have all := EvalsToInTime.trans _ _ _ _ _ _ first right
  change EvalsToInTime steinerUnaryArcQueryMachine.step _
    (some (unaryArcCfg (some .nextRow) (unaryArcState (found || (decide (a = q₁) && decide (b = q₂)))) input q₁ q₂ 0)) _ at all
  rw [unaryArc_row_match] at all
  exact ⟨all.toEvalsTo,by have paid := all.steps_le_m; omega⟩

private def unaryArc_rows (q₁ q₂ : ℕ) (rows : List (ℕ × ℕ)) (found : Bool) :
    EvalsToInTime steinerUnaryArcQueryMachine.step
      (unaryArcCfg (some .nextRow) (unaryArcState found) (encodeSteinerUnaryArcRows rows) q₁ q₂ 0)
      (some (unaryArcCfg (some (.clear .first)) (unaryArcState (found || decide ((q₁,q₂) ∈ rows))) [] q₁ q₂ 0))
      (3*(encodeSteinerUnaryArcRows rows).length+1) := by
  induction rows generalizing found with
  | nil =>
    simpa only [List.not_mem_nil,decide_false,Bool.or_false,encodeSteinerUnaryArcRows,
      encodeSteinerUnaryEndpointValues,List.flatMap_nil,List.length_nil,Nat.mul_zero,Nat.zero_add]
      using unaryArc_one (unaryArc_endRows q₁ q₂ found)
  | cons row rows ih =>
    obtain ⟨a,b⟩ := row
    have first := unaryArc_row q₁ q₂ a b (encodeSteinerUnaryArcRows rows) found
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (found || decide ((q₁,q₂) = (a,b))))
    rw [encodeSteinerUnaryArcRows_cons]
    simp only [List.mem_cons,Bool.decide_or,← Bool.or_assoc]
    refine ⟨all.toEvalsTo,all.steps_le_m.trans ?_⟩
    simp only [List.length_append,List.length_replicate,List.length_cons]
    omega

abbrev SteinerUnaryArcQuery := (ℕ × ℕ) × List (ℕ × ℕ)

/-- The query precedes the raw graph rows in the same unary format. -/
def encodeSteinerUnaryArcQuery (request : SteinerUnaryArcQuery) : List (Option Bool) :=
  encodeSteinerUnaryArcRows (request.1::request.2)

theorem encodeSteinerUnaryArcQuery_append (arc : ℕ × ℕ) (rows : List (ℕ × ℕ)) :
    encodeSteinerUnaryArcQuery (arc,rows) = encodeSteinerUnaryArcRows [arc]++encodeSteinerUnaryArcRows rows := by
  exact encodeSteinerUnaryArcRows_append [arc] rows

def steinerUnaryArcQueryAnswer (request : SteinerUnaryArcQuery) : List (Option Bool) :=
  [some (decide (request.1 ∈ request.2))]

private theorem unaryArc_init (word : List (Option Bool)) :
    initList steinerUnaryArcQueryMachine word = unaryArcCfg (some (.loadQuery .first)) (unaryArcState false) word 0 0 0 := by
  apply congrArg (fun stk : Fin 4 → List (Option Bool) =>
    (⟨some (.loadQuery .first),unaryArcState false,stk⟩ : steinerUnaryArcQueryMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem unaryArc_halt (answer : Bool) :
    haltList steinerUnaryArcQueryMachine [some answer] = unaryArcCfg none (unaryArcState false) [some answer] 0 0 0 := by
  apply congrArg (fun stk : Fin 4 → List (Option Bool) =>
    (⟨none,unaryArcState false,stk⟩ : steinerUnaryArcQueryMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- The actual finite machine tests membership in at most three
transitions per complete framed input symbol plus one. -/
def steinerUnaryArcQueryMachine_run (request : SteinerUnaryArcQuery) :
    TM2OutputsInTime steinerUnaryArcQueryMachine (encodeSteinerUnaryArcQuery request)
      (some (steinerUnaryArcQueryAnswer request)) (3*(encodeSteinerUnaryArcQuery request).length+1) := by
  rcases request with ⟨⟨a,b⟩,rows⟩
  let frame := encodeSteinerUnaryArcRows rows
  let found := decide ((a,b) ∈ rows)
  have left := unaryArc_load .first a 0 0 (arcTallies b++none::frame)
  have right := unaryArc_load .second b 0 a frame
  rw [Nat.zero_add] at left right
  have start := EvalsToInTime.trans _ _ _ _ _ _ left right
  have result := unaryArc_rows a b rows false
  rw [Bool.false_or] at result
  have scanned := EvalsToInTime.trans _ _ _ _ _ _ start result
  have cleared := EvalsToInTime.trans _ _ _ _ _ _ scanned (unaryArc_clear .first a b found)
  have all := EvalsToInTime.trans _ _ _ _ _ _ cleared (unaryArc_clear .second b 0 found)
  change EvalsToInTime steinerUnaryArcQueryMachine.step _ (some (haltList steinerUnaryArcQueryMachine [some found])) _
  rw [unaryArc_init,unaryArc_halt]
  unfold encodeSteinerUnaryArcQuery
  rw [encodeSteinerUnaryArcRows_cons]
  refine ⟨all.toEvalsTo,all.steps_le_m.trans ?_⟩
  simp only [List.length_append,List.length_replicate,List.length_cons]
  omega

/-- The graph membership test is linear in the framed query and arc rows. -/
noncomputable def steinerUnaryArcQueryMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryArcQuery id steinerUnaryArcQueryAnswer where
  tm := steinerUnaryArcQueryMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 3*Polynomial.X+Polynomial.C 1
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,
      Polynomial.eval_X,Polynomial.eval_C]
      using steinerUnaryArcQueryMachine_run request

/-- Encode finite arc names by their two numerical indices. -/
def steinerUnaryArcValues {n : ℕ} (arc : Fin n × Fin n) : ℕ × ℕ := (arc.1.val,arc.2.val)

/-- The unary row encoding is exactly the accepted graph decoder's payload. -/
theorem encodeSteinerUnaryArcRows_finite {n : ℕ} (rows : List (Fin n × Fin n)) :
    encodeSteinerUnaryArcRows (rows.map steinerUnaryArcValues) =
      encodeSteinerUnaryEndpointValues (rows.flatMap fun arc => [arc.1.val,arc.2.val]) := by
  simp only [encodeSteinerUnaryArcRows,List.flatMap_map,steinerUnaryArcValues]

theorem steinerUnaryArcValues_mem_finset {n : ℕ} (arc : Fin n × Fin n) (rows : List (Fin n × Fin n)) :
    steinerUnaryArcValues arc ∈ rows.map steinerUnaryArcValues ↔ arc ∈ rows.toFinset := by
  have injective : Function.Injective (steinerUnaryArcValues (n := n)) := by
    intro a b eq
    exact Prod.ext (Fin.ext (congrArg Prod.fst eq)) (Fin.ext (congrArg Prod.snd eq))
  rw [List.mem_toFinset,List.mem_map]
  exact ⟨fun ⟨found,inside,eq⟩ => injective eq ▸ inside,fun inside => ⟨arc,inside,rfl⟩⟩

/-- On a list of checked finite arcs the output is exactly membership
in the graph obtained by taking their finite set. -/
def steinerUnaryArcQueryMachine_finset {n : ℕ} (arc : Fin n × Fin n) (rows : List (Fin n × Fin n)) :
    let request : SteinerUnaryArcQuery := (steinerUnaryArcValues arc,rows.map steinerUnaryArcValues)
    TM2OutputsInTime steinerUnaryArcQueryMachine (encodeSteinerUnaryArcQuery request)
      (some [some (decide (arc ∈ rows.toFinset))]) (3*(encodeSteinerUnaryArcQuery request).length+1) := by
  let request : SteinerUnaryArcQuery := (steinerUnaryArcValues arc,rows.map steinerUnaryArcValues)
  simpa only [steinerUnaryArcQueryAnswer,request,Prod.fst,Prod.snd,steinerUnaryArcValues_mem_finset]
    using steinerUnaryArcQueryMachine_run request

end OnlineReachabilityPreservers
