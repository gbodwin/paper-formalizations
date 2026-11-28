import OnlineReachabilityPreservers.SteinerUnaryRoundPriorArchiveMachine

/-! Accumulate the rooted vector totals into the positive forest scale. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev TotalSymbol := SteinerUnaryCappedRowsSymbol
private abbrev TotalRegister := Option TotalSymbol
private abbrev TotalProgram := StackMachineTag.Program (Fin 2) TotalSymbol PUnit TotalRegister

private def roundTally : TotalSymbol := Sum.inr (some true)

private def roundTotalIsTally : TotalSymbol → Bool
  | .inr (some true) => true
  | _ => false

private def roundTotalRead (_ : TotalRegister) (symbol : Option TotalSymbol) : TotalRegister := symbol

private def roundTotalStop : TotalProgram := load (fun _ => none) halt

private def roundTotalRepeat : TotalProgram := load (fun _ => none) (goto fun _ => PUnit.unit)

private def roundTotalProgram (positive : Bool) (_ : PUnit) : TotalProgram :=
  pop 0 roundTotalRead <|
    branch Option.isSome
      (branch (fun r => roundTotalIsTally (r.getD (Sum.inl false)))
        (push 1 (fun _ => roundTally) roundTotalRepeat) roundTotalRepeat)
      (if positive then
        peek 1 roundTotalRead <| branch Option.isSome roundTotalStop
          (push 1 (fun _ => roundTally) roundTotalStop)
       else roundTotalStop)

/-- Accumulate unary totals on the second stack. The final call may
supply a single tally when the accumulated value is zero. -/
abbrev steinerUnaryRoundTotalMachine (positive : Bool) : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 1
  Γ _ := TotalSymbol
  Λ := PUnit
  main := PUnit.unit
  σ := TotalRegister
  initialState := none
  m := roundTotalProgram positive

/-- The scale tally uses the same tally symbols as the distance rounds. -/
def encodeSteinerUnaryRoundTotal (value : ℕ) : List SteinerUnaryCappedRowsSymbol :=
  List.replicate value roundTally

/-- Configuration with a live row frame and a possibly nonempty accumulator. -/
def steinerUnaryRoundTotalCfg (positive : Bool) (label : Option PUnit)
    (input : List SteinerUnaryCappedRowsSymbol) (total : ℕ) : (steinerUnaryRoundTotalMachine positive).Cfg :=
  ⟨label,none,![input,encodeSteinerUnaryRoundTotal total]⟩

private theorem roundTotal_update0 (a b word : List TotalSymbol) :
    Function.update (![a,b] : Fin 2 → List TotalSymbol) 0 word = ![word,b] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem roundTotal_update1 (a b word : List TotalSymbol) :
    Function.update (![a,b] : Fin 2 → List TotalSymbol) 1 word = ![a,word] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem roundTotalStep (positive : Bool) (symbol : TotalSymbol) (word : List TotalSymbol) (total : ℕ) :
    (steinerUnaryRoundTotalMachine positive).step
      (steinerUnaryRoundTotalCfg positive (some PUnit.unit) (symbol::word) total) =
      some (steinerUnaryRoundTotalCfg positive (some PUnit.unit) word
        (if roundTotalIsTally symbol then total+1 else total)) := by
  cases marked : roundTotalIsTally symbol <;>
    simp only [FinTM2.step,steinerUnaryRoundTotalMachine,steinerUnaryRoundTotalCfg,Turing.TM2.step,Turing.TM2.stepAux,
      roundTotalProgram,roundTotalRead,roundTotal_update0,roundTotal_update1,roundTotalRepeat,Matrix.cons_val_zero,
      List.tail_cons,List.head?_cons,Option.isSome_some,Option.getD_some,Bool.cond_true,Bool.cond_false,marked,
      Bool.false_eq_true,ite_false,ite_true,encodeSteinerUnaryRoundTotal,List.replicate_succ] <;> rfl

private theorem roundTotalEnd (positive : Bool) (total : ℕ) :
    (steinerUnaryRoundTotalMachine positive).step (steinerUnaryRoundTotalCfg positive (some PUnit.unit) [] total) =
      some (steinerUnaryRoundTotalCfg positive none [] (if positive then max 1 total else total)) := by
  cases positive <;> cases total <;>
    simp only [FinTM2.step,steinerUnaryRoundTotalMachine,steinerUnaryRoundTotalCfg,Turing.TM2.step,Turing.TM2.stepAux,
      roundTotalProgram,roundTotalRead,roundTotal_update0,roundTotal_update1,roundTotalStop,
      encodeSteinerUnaryRoundTotal,List.replicate_succ,ite_true,Bool.false_eq_true,ite_false,zero_le, max_eq_left,
      Nat.le_add_left,max_eq_right] <;> rfl

private def roundTotalOne (positive : Bool) {a b : (steinerUnaryRoundTotalMachine positive).Cfg}
    (move : (steinerUnaryRoundTotalMachine positive).step a = some b) :
    EvalsToInTime (steinerUnaryRoundTotalMachine positive).step a (some b) 1 := ⟨⟨1,move⟩,le_rfl⟩

private def roundTotalRaw (positive : Bool) (word : List TotalSymbol) (total : ℕ) :
    let all := total+(word.filter roundTotalIsTally).length
    EvalsToInTime (steinerUnaryRoundTotalMachine positive).step
      (steinerUnaryRoundTotalCfg positive (some PUnit.unit) word total)
      (some (steinerUnaryRoundTotalCfg positive none [] (if positive then max 1 all else all))) (word.length+1) := by
  induction word generalizing total with
  | nil => exact roundTotalOne positive (roundTotalEnd positive total)
  | cons symbol word ih =>
    have run := EvalsToInTime.trans _ _ _ _ _ _ (roundTotalOne positive (roundTotalStep positive symbol word total))
      (ih (if roundTotalIsTally symbol then total+1 else total))
    by_cases marked : roundTotalIsTally symbol
    · simpa only [ite_eq_left marked,List.filter_cons_of_pos marked,List.length_cons,Nat.add_right_comm,
        Nat.add_assoc] using run
    · simpa only [ite_eq_right marked,List.filter_cons_of_neg marked,List.length_cons] using run

private theorem roundTotal_count (values : List ℕ) :
    ((encodeSteinerUnaryCappedRowTallies values).filter roundTotalIsTally).length = values.sum := by
  induction values with
  | nil => rfl
  | cons value tail ih =>
    change ((List.replicate value roundTally++[Sum.inl true]++encodeSteinerUnaryCappedRowTallies tail).filter
      roundTotalIsTally).length = _
    rw [List.filter_append,List.filter_append,List.length_append,List.length_append,ih]
    simp [roundTally,roundTotalIsTally,List.filter_replicate]

/-- Native row summation from a live tally of earlier vectors. Each
input symbol takes one transition, followed by the final floor test. -/
def steinerUnaryRoundTotalMachine_run (positive : Bool) (values : List ℕ) (total : ℕ) :
    let word := encodeSteinerUnaryCappedRowTallies values
    let all := total+values.sum
    EvalsToInTime (steinerUnaryRoundTotalMachine positive).step
      (steinerUnaryRoundTotalCfg positive (some PUnit.unit) word total)
      (some (steinerUnaryRoundTotalCfg positive none [] (if positive then max 1 all else all))) (word.length+1) := by
  simpa only [roundTotal_count] using roundTotalRaw positive (encodeSteinerUnaryCappedRowTallies values) total

private theorem roundTotal_vector_sum {n : ℕ} (values : Vector ℕ n) :
    values.toList.sum = ∑ i : Fin n, values[i.val] := by
  have same : Vector.ofFn (fun i : Fin n => values[i.val]) = values := by
    ext i hi
    simp
  rw [← same,Vector.toList_ofFn,List.sum_ofFn]
  simp

/-- Accumulate the original orientation, add the reverse orientation,
and apply the floor to obtain the distance-table forest scale. -/
theorem forestScaleFromDistanceRounds_eq_vectorTotals {n : ℕ} (dist : Fin n × Fin n → ℕ) (height : ℕ) :
    forestScaleFromDistanceRounds dist height =
      max 1 ((inwardHeightWeightRounds dist height).toList.sum+
        (inwardHeightWeightRounds (fun d => dist d.swap) height).toList.sum) := by
  simp only [forestScaleFromDistanceRounds,Finset.sum_add_distrib,roundTotal_vector_sum]

end OnlineReachabilityPreservers
