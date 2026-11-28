import OnlineReachabilityPreservers.SteinerSeedTapeMachine
import OnlineReachabilityPreservers.SteinerBinaryArithmetic
import OnlineReachabilityPreservers.SteinerBinaryReachWork

/-! One finite stack machine for numeric and exact bit-word comparison. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev ComparisonSymbol := Option Bool
private abbrev ComparisonFlags := Bool × Bool
private abbrev ComparisonRegister := ComparisonFlags × (Option ComparisonSymbol × Option ComparisonSymbol)
private abbrev ComparisonStmt :=
  Turing.TM2.Stmt (fun _ : Fin 3 => ComparisonSymbol) (Fin 3) ComparisonRegister

private def comparisonClear (register : ComparisonRegister) : ComparisonRegister :=
  (register.1,(none,none))

private def comparisonLeft (register : ComparisonRegister) (value : Option ComparisonSymbol) : ComparisonRegister :=
  (register.1,(value,register.2.2))

private def comparisonRight (register : ComparisonRegister) (value : Option ComparisonSymbol) : ComparisonRegister :=
  (register.1,(register.2.1,value))

private def comparisonAdvance (flags : ComparisonFlags) (left right : Option Bool) : ComparisonFlags :=
  (nextBinaryBorrow (left.getD false) (right.getD false) flags.1,flags.2 && (left == right))

private def binaryComparisonProgram (label : Fin 3) : ComparisonStmt :=
  if label = 0 then
    peek 0 comparisonLeft <|
      branch (fun register => register.2.1.join.isSome)
        (pop 0 comparisonLeft <| push 1 (fun register => register.2.1.getD none) <|
          load comparisonClear <| goto (fun _ => 0))
        (pop 0 (fun register _ => comparisonClear register) <| goto (fun _ => 1))
  else if label = 1 then
    peek 1 comparisonLeft <|
      branch (fun register => register.2.1.isSome)
        (pop 1 comparisonLeft <| push 2 (fun register => register.2.1.getD none) <|
          load comparisonClear <| goto (fun _ => 1))
        (load comparisonClear <| goto (fun _ => 2))
  else
    peek 2 comparisonLeft <| peek 0 comparisonRight <|
      branch (fun register => register.2.1.isSome || register.2.2.isSome)
        (pop 2 (fun register _ => register) <| pop 0 (fun register _ => register) <|
          load (fun register => (comparisonAdvance register.1 register.2.1.join register.2.2.join,(none,none))) <|
          goto (fun _ => 2))
        (push 0 (fun register => some register.1.2) <| push 0 (fun register => some register.1.1) <|
          load (fun _ => ((false,true),(none,none))) halt)

/-- The first word appears before a separator. Copy it through two
stacks to compare the two words from their low bits. Return the
numeric less-than flag followed by the exact-list equality flag. -/
abbrev steinerBinaryComparisonMachine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 0
  Γ _ := ComparisonSymbol
  Λ := Fin 3
  main := 0
  σ := ComparisonRegister
  initialState := ((false,true),(none,none))
  m := binaryComparisonProgram

private def comparisonConfig (label : Option (Fin 3)) (flags : ComparisonFlags)
    (input reverse forward : List ComparisonSymbol) : steinerBinaryComparisonMachine.Cfg where
  l := label
  var := (flags,(none,none))
  stk := ![input,reverse,forward]

private theorem comparison_load_bit (flags : ComparisonFlags) (bit : Bool)
    (input reverse forward : List ComparisonSymbol) :
    steinerBinaryComparisonMachine.step (comparisonConfig (some 0) flags (some bit::input) reverse forward) =
      some (comparisonConfig (some 0) flags input (some bit::reverse) forward) := by
  simp [FinTM2.step,steinerBinaryComparisonMachine,comparisonConfig,Turing.TM2.step,Turing.TM2.stepAux,
    binaryComparisonProgram,comparisonLeft,comparisonClear,tapeStack_update_input,tapeStack_update_markers]
  rfl

private theorem comparison_load_separator (flags : ComparisonFlags) (input reverse forward : List ComparisonSymbol) :
    steinerBinaryComparisonMachine.step (comparisonConfig (some 0) flags (none::input) reverse forward) =
      some (comparisonConfig (some 1) flags input reverse forward) := by
  simp [FinTM2.step,steinerBinaryComparisonMachine,comparisonConfig,Turing.TM2.step,Turing.TM2.stepAux,
    binaryComparisonProgram,comparisonLeft,comparisonClear,tapeStack_update_input]
  rfl

private theorem comparison_reverse_step (flags : ComparisonFlags) (bit : ComparisonSymbol)
    (input reverse forward : List ComparisonSymbol) :
    steinerBinaryComparisonMachine.step (comparisonConfig (some 1) flags input (bit::reverse) forward) =
      some (comparisonConfig (some 1) flags input reverse (bit::forward)) := by
  simp [FinTM2.step,steinerBinaryComparisonMachine,comparisonConfig,Turing.TM2.step,Turing.TM2.stepAux,
    binaryComparisonProgram,comparisonLeft,comparisonClear,tapeStack_update_markers,tapeStack_update_work]
  rfl

private theorem comparison_reverse_end (flags : ComparisonFlags) (input forward : List ComparisonSymbol) :
    steinerBinaryComparisonMachine.step (comparisonConfig (some 1) flags input [] forward) =
      some (comparisonConfig (some 2) flags input [] forward) := by
  simp [FinTM2.step,steinerBinaryComparisonMachine,comparisonConfig,Turing.TM2.step,Turing.TM2.stepAux,
    binaryComparisonProgram,comparisonLeft,comparisonClear]
  rfl

private theorem comparison_consume (flags : ComparisonFlags) (left right : List Bool)
    (nonempty : ¬ (left = [] ∧ right = [])) :
    steinerBinaryComparisonMachine.step (comparisonConfig (some 2) flags (right.map some) [] (left.map some)) =
      some (comparisonConfig (some 2) (comparisonAdvance flags left.head? right.head?)
        (right.tail.map some) [] (left.tail.map some)) := by
  cases left <;> cases right
  · exact (nonempty ⟨rfl,rfl⟩).elim
  all_goals
    simp [FinTM2.step,steinerBinaryComparisonMachine,comparisonConfig,Turing.TM2.step,Turing.TM2.stepAux,
      binaryComparisonProgram,comparisonLeft,comparisonRight,tapeStack_update_input,tapeStack_update_work]
    rfl

private theorem comparison_end (flags : ComparisonFlags) :
    steinerBinaryComparisonMachine.step (comparisonConfig (some 2) flags [] [] []) =
      some (comparisonConfig none (false,true) [some flags.1,some flags.2] [] []) := by
  simp [FinTM2.step,steinerBinaryComparisonMachine,comparisonConfig,Turing.TM2.step,Turing.TM2.stepAux,
    binaryComparisonProgram,comparisonLeft,comparisonRight,tapeStack_update_input]
  rfl

private def comparisonSingleStep {before after : steinerBinaryComparisonMachine.Cfg}
    (step : steinerBinaryComparisonMachine.step before = some after) :
    EvalsToInTime steinerBinaryComparisonMachine.step before (some after) 1 where
  steps := 1
  evals_in_steps := by change steinerBinaryComparisonMachine.step before = _; exact step
  steps_le_m := le_rfl

private def comparison_load_run (left right : List Bool) (flags : ComparisonFlags)
    (reverse forward : List ComparisonSymbol) :
    EvalsToInTime steinerBinaryComparisonMachine.step
      (comparisonConfig (some 0) flags (left.map some ++ none::right.map some) reverse forward)
      (some (comparisonConfig (some 1) flags (right.map some) (left.reverse.map some ++ reverse) forward))
      (left.length+1) := by
  induction left generalizing reverse with
  | nil => simpa using comparisonSingleStep (comparison_load_separator flags (right.map some) reverse forward)
  | cons bit left ih =>
    have first := comparisonSingleStep
      (comparison_load_bit flags bit (left.map some ++ none::right.map some) reverse forward)
    have rest := ih (some bit::reverse)
    have both := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [List.length_cons,List.map_cons,List.cons_append,List.reverse_cons,List.map_append,
      List.map_nil,List.nil_append,List.singleton_append,List.append_assoc] using both

private def comparison_reverse_run (reverse input forward : List ComparisonSymbol) (flags : ComparisonFlags) :
    EvalsToInTime steinerBinaryComparisonMachine.step (comparisonConfig (some 1) flags input reverse forward)
      (some (comparisonConfig (some 2) flags input [] (reverse.reverse ++ forward))) (reverse.length+1) := by
  induction reverse generalizing forward with
  | nil => simpa using comparisonSingleStep (comparison_reverse_end flags input forward)
  | cons bit reverse ih =>
    have first := comparisonSingleStep (comparison_reverse_step flags bit input reverse forward)
    have rest := ih (bit::forward)
    have both := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using both

private theorem comparison_less_recurrence (left right : List Bool) (flags : ComparisonFlags)
    (nonempty : ¬ (left = [] ∧ right = [])) :
    (binaryLessWithWork left right flags.1).1 =
      (binaryLessWithWork left.tail right.tail (comparisonAdvance flags left.head? right.head?).1).1 := by
  rw [binaryLessWithWork,dite_eq_right nonempty]
  cases left <;> cases right <;> rfl

private theorem comparison_equal_recurrence (left right : List Bool) (flags : ComparisonFlags) :
    (flags.2 && (binaryEqualWithWork left right).1) =
      ((comparisonAdvance flags left.head? right.head?).2 && (binaryEqualWithWork left.tail right.tail).1) := by
  simp only [(binaryEqualWithWork_spec _ _).1]
  cases left <;> cases right <;> simp [comparisonAdvance,List.cons.injEq,Bool.and_assoc]
  rename_i leftBit _ rightBit _
  cases leftBit <;> cases rightBit <;> rfl

private def comparison_run_ends (left right : List Bool) (flags : ComparisonFlags) :
    EvalsToInTime steinerBinaryComparisonMachine.step
      (comparisonConfig (some 2) flags (right.map some) [] (left.map some))
      (some (comparisonConfig none (false,true)
        [some (binaryLessWithWork left right flags.1).1,some (flags.2 && (binaryEqualWithWork left right).1)] [] []))
      (left.length+right.length+1) := by
  by_cases empty : left = [] ∧ right = []
  · obtain ⟨rfl,rfl⟩ := empty
    simpa [binaryLessWithWork,binaryEqualWithWork] using comparisonSingleStep (comparison_end flags)
  have shorter : left.tail.length+right.tail.length < left.length+right.length := by
    cases left <;> cases right <;> simp_all
    omega
  have first := comparisonSingleStep (comparison_consume flags left right empty)
  have rest := comparison_run_ends left.tail right.tail (comparisonAdvance flags left.head? right.head?)
  have both := EvalsToInTime.trans _ _ _ _ _ _ first rest
  have paid := both.steps_le_m
  have within : both.steps ≤ left.length+right.length+1 := by omega
  rw [comparison_less_recurrence left right flags empty,comparison_equal_recurrence left right flags]
  exact ⟨both.toEvalsTo,within⟩
termination_by left.length+right.length
decreasing_by exact shorter

private theorem binaryComparisonMachine_init (input : List ComparisonSymbol) :
    initList steinerBinaryComparisonMachine input = comparisonConfig (some 0) (false,true) input [] [] := by
  unfold initList comparisonConfig
  apply congrArg (fun stk : Fin 3 → List ComparisonSymbol =>
    (⟨some (0:Fin 3),((false,true),(none,none)),stk⟩ : steinerBinaryComparisonMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem binaryComparisonMachine_halt (output : List ComparisonSymbol) :
    haltList steinerBinaryComparisonMachine output = comparisonConfig none (false,true) output [] [] := by
  unfold haltList comparisonConfig
  apply congrArg (fun stk : Fin 3 → List ComparisonSymbol =>
    (⟨none,((false,true),(none,none)),stk⟩ : steinerBinaryComparisonMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- Pack two least-significant-bit-first words with a separator. -/
def encodeSteinerBinaryComparison (words : List Bool × List Bool) : List (Option Bool) :=
  words.1.map some ++ none::words.2.map some

/-- Return numeric less-than and exact bit-list equality. -/
def steinerBinaryComparisonOutput (words : List Bool × List Bool) : List (Option Bool) :=
  [some (binaryLessWithWork words.1 words.2 false).1,some (binaryEqualWithWork words.1 words.2).1]

/-- Machine transitions account for copying the first word and
consuming both words. The flags agree with the measured primitives. -/
def steinerBinaryComparisonMachine_run (words : List Bool × List Bool) :
    TM2OutputsInTime steinerBinaryComparisonMachine (encodeSteinerBinaryComparison words)
      (some (steinerBinaryComparisonOutput words)) (3*words.1.length+words.2.length+3) := by
  obtain ⟨left,right⟩ := words
  have starting := comparison_load_run left right (false,true) [] []
  simp only [List.append_nil] at starting
  have reversed := comparison_reverse_run (left.reverse.map some) (right.map some) [] (false,true)
  rw [List.append_nil,← List.map_reverse,List.reverse_reverse,List.length_map,List.length_reverse] at reversed
  have comparing := comparison_run_ends left right (false,true)
  simp only [Bool.true_and] at comparing
  have prepared := EvalsToInTime.trans _ _ _ _ _ _ starting reversed
  have run := EvalsToInTime.trans _ _ _ _ _ _ prepared comparing
  unfold TM2OutputsInTime
  change EvalsToInTime steinerBinaryComparisonMachine.step _ (some (haltList steinerBinaryComparisonMachine _)) _
  rw [binaryComparisonMachine_init,binaryComparisonMachine_halt]
  have count : left.length+right.length+1+(left.length+1+(left.length+1)) =
      3*left.length+right.length+3 := by omega
  simpa only [encodeSteinerBinaryComparison,steinerBinaryComparisonOutput,count] using run

/-- The first flag compares numeric values, even with high zero bits.
The second compares the original bit lists. -/
theorem steinerBinaryComparisonOutput_spec (words : List Bool × List Bool) :
    steinerBinaryComparisonOutput words =
      [some (decide (binaryWordValue words.1 < binaryWordValue words.2)),some (decide (words.1 = words.2))] := by
  simp only [steinerBinaryComparisonOutput,(binaryLessWithWork_noBorrow_spec _ _).1,(binaryEqualWithWork_spec _ _).1]

/-- The two comparisons are linear in the size of the separated
input words in Mathlib's finite-stack model. -/
noncomputable def steinerBinaryComparisonMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerBinaryComparison id steinerBinaryComparisonOutput where
  tm := steinerBinaryComparisonMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 3 * Polynomial.X
  outputsFun words := by
    have run := steinerBinaryComparisonMachine_run words
    have bound : 3*words.1.length+words.2.length+3 ≤
        (Polynomial.C 3 * Polynomial.X).eval (encodeSteinerBinaryComparison words).length := by
      simp [encodeSteinerBinaryComparison]
      omega
    change TM2OutputsInTime steinerBinaryComparisonMachine ((encodeSteinerBinaryComparison words).map id)
      (some ((steinerBinaryComparisonOutput words).map id)) _
    simpa only [List.map_id_fun,id_eq] using
      (show TM2OutputsInTime steinerBinaryComparisonMachine (encodeSteinerBinaryComparison words)
        (some (steinerBinaryComparisonOutput words)) _ from ⟨run.toEvalsTo,run.steps_le_m.trans bound⟩)

/-- With a supplied word for the vertex budget, the numeric flag
indicates whether the decoded endpoint is a valid vertex label. -/
def steinerBinaryComparisonMachine_endpoint (label bound : List Bool) {n : ℕ}
    (budget : binaryWordValue bound = n) :
    TM2OutputsInTime steinerBinaryComparisonMachine (encodeSteinerBinaryComparison (label,bound))
      (some [some (decide (binaryWordValue label < n)),some (decide (label = bound))])
      (3*label.length+bound.length+3) := by
  have run := steinerBinaryComparisonMachine_run (label,bound)
  rw [steinerBinaryComparisonOutput_spec] at run
  simpa only [Prod.fst,Prod.snd,budget] using run

end OnlineReachabilityPreservers
