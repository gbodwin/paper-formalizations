import OnlineReachabilityPreservers.SteinerUnaryDistanceRoundFrameMachine

/-! Turn the output of one forest round into the archived vector for the next. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev RoundPriorSymbol := SteinerUnaryCappedRowsSymbol
private abbrev RoundPriorProgram := StackMachineTag.Program (Fin 2) RoundPriorSymbol PUnit (Option RoundPriorSymbol)

private def roundPriorSymbol : RoundPriorSymbol → RoundPriorSymbol
  | .inl true => .inr none
  | symbol => symbol

private def roundPriorProgram (_ : PUnit) : RoundPriorProgram :=
  pop 0 (fun _ seen => seen) <|
    branch Option.isSome
      (push 1 (fun r => roundPriorSymbol (r.getD (Sum.inl false))) <|
        load (fun _ => none) (goto fun _ => PUnit.unit))
      (load (fun _ => none) halt)

/-- Store the next previous-weight vector in reverse order, replacing
each output row marker with an operand-field delimiter. -/
abbrev steinerUnaryRoundPriorArchiveMachine : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 1
  Γ _ := RoundPriorSymbol
  Λ := PUnit
  main := PUnit.unit
  σ := Option RoundPriorSymbol
  initialState := none
  m := roundPriorProgram

private def roundPriorCfg (label : Option PUnit) (input archive : List RoundPriorSymbol) :
    steinerUnaryRoundPriorArchiveMachine.Cfg where
  l := label
  var := none
  stk := ![input,archive]

private theorem roundPrior_update0 (input archive word : List RoundPriorSymbol) :
    Function.update (![input,archive] : Fin 2 → List RoundPriorSymbol) 0 word = ![word,archive] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem roundPrior_update1 (input archive word : List RoundPriorSymbol) :
    Function.update (![input,archive] : Fin 2 → List RoundPriorSymbol) 1 word = ![input,word] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem roundPrior_move (symbol : RoundPriorSymbol) (input archive : List RoundPriorSymbol) :
    steinerUnaryRoundPriorArchiveMachine.step (roundPriorCfg (some PUnit.unit) (symbol::input) archive) =
      some (roundPriorCfg (some PUnit.unit) input (roundPriorSymbol symbol::archive)) := by
  simp [FinTM2.step,steinerUnaryRoundPriorArchiveMachine,roundPriorCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundPriorProgram,roundPrior_update0,roundPrior_update1]
  rfl

private theorem roundPrior_end (archive : List RoundPriorSymbol) :
    steinerUnaryRoundPriorArchiveMachine.step (roundPriorCfg (some PUnit.unit) [] archive) =
      some (roundPriorCfg none [] archive) := by
  simp [FinTM2.step,steinerUnaryRoundPriorArchiveMachine,roundPriorCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundPriorProgram,roundPrior_update0]
  rfl

private def roundPrior_one {a b : steinerUnaryRoundPriorArchiveMachine.Cfg}
    (step : steinerUnaryRoundPriorArchiveMachine.step a = some b) :
    EvalsToInTime steinerUnaryRoundPriorArchiveMachine.step a (some b) 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := step

private def roundPrior_run (word archive : List RoundPriorSymbol) :
    EvalsToInTime steinerUnaryRoundPriorArchiveMachine.step (roundPriorCfg (some PUnit.unit) word archive)
      (some (roundPriorCfg none [] ((word.map roundPriorSymbol).reverse++archive))) (word.length+1) := by
  induction word generalizing archive with
  | nil => exact roundPrior_one (roundPrior_end archive)
  | cons symbol word ih =>
    have run := EvalsToInTime.trans _ _ _ _ _ _
      (roundPrior_one (roundPrior_move symbol word archive)) (ih (roundPriorSymbol symbol::archive))
    simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons] using run

private theorem roundPrior_init (word : List RoundPriorSymbol) :
    initList steinerUnaryRoundPriorArchiveMachine word = roundPriorCfg (some PUnit.unit) word [] := by
  apply congrArg (fun stk : Fin 2 → List RoundPriorSymbol =>
    (⟨some PUnit.unit,none,stk⟩ : steinerUnaryRoundPriorArchiveMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem roundPrior_halt (word : List RoundPriorSymbol) :
    haltList steinerUnaryRoundPriorArchiveMachine word = roundPriorCfg none [] word := by
  apply congrArg (fun stk : Fin 2 → List RoundPriorSymbol =>
    (⟨none,none,stk⟩ : steinerUnaryRoundPriorArchiveMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- Encode a vector as a sequence of delimited unary values. -/
def encodeSteinerUnaryRoundPriorVector (values : List ℕ) : List SteinerUnaryCappedRowsSymbol :=
  values.flatMap fun value => List.replicate value (Sum.inr (some true))++[Sum.inr none]

/-- One field delimiter follows each value, including zero. -/
theorem encodeSteinerUnaryRoundPriorVector_length (values : List ℕ) :
    (encodeSteinerUnaryRoundPriorVector values).length = values.sum+values.length := by
  induction values with
  | nil => rfl
  | cons value tail ih =>
    change (List.replicate value (Sum.inr (some true))++[Sum.inr none]++encodeSteinerUnaryRoundPriorVector tail).length = _
    simp only [List.length_append,List.length_replicate,List.length_nil,List.length_cons,List.sum_cons,ih]
    omega

theorem encodeSteinerUnaryRoundPriorVector_zero (n : ℕ) :
    encodeSteinerUnaryRoundPriorVector (List.replicate n 0) = List.replicate n (Sum.inr none) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Sum.inr none::encodeSteinerUnaryRoundPriorVector (List.replicate n 0) = _
    rw [ih]
    rfl

theorem encodeSteinerUnaryRoundPriorVector_length_le {n B : ℕ} (values : Vector ℕ n)
    (bound : ∀ i : Fin n, values[i.val] ≤ B) :
    (encodeSteinerUnaryRoundPriorVector values.toList).length ≤ n*(B+1) := by
  rw [encodeSteinerUnaryRoundPriorVector_length,Vector.length_toList,Nat.mul_add,Nat.mul_one]
  apply Nat.add_le_add_right
  have entries (value : ℕ) (mem : value ∈ values.toList) : value ≤ B := by
    obtain ⟨i,hi,same⟩ := List.mem_iff_getElem.mp mem
    have valid : i < n := by simpa only [Vector.length_toList] using hi
    rw [← same,Vector.getElem_toList]
    exact bound ⟨i,valid⟩
  have sum_le (entries : List ℕ) (bounded : ∀ value ∈ entries, value ≤ B) :
      entries.sum ≤ entries.length*B := by
    induction entries with
    | nil => simp
    | cons value tail ih =>
      simp only [List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      have head := bounded value (List.mem_cons_self ..)
      have rest := ih fun value mem => bounded value (List.mem_cons_of_mem _ mem)
      omega
  simpa only [Vector.length_toList] using sum_le values.toList entries

/-- Restore an archived weight field to the output row format. -/
def steinerUnaryRoundPriorToRow : SteinerUnaryCappedRowsSymbol → SteinerUnaryCappedRowsSymbol
  | .inr none => .inl true
  | symbol => symbol

theorem encodeSteinerUnaryRoundPriorVector_map_toRows (totals : List ℕ) :
    (encodeSteinerUnaryRoundPriorVector totals).map steinerUnaryRoundPriorToRow =
      encodeSteinerUnaryCappedRowTallies totals := by
  induction totals with
  | nil => rfl
  | cons total totals ih =>
    change ((List.replicate total (Sum.inr (some true))++[Sum.inr none])++
      encodeSteinerUnaryRoundPriorVector totals).map steinerUnaryRoundPriorToRow =
      (List.replicate total (Sum.inr (some true))++[Sum.inl true])++encodeSteinerUnaryCappedRowTallies totals
    simp only [List.map_append,List.map_replicate,List.map_singleton,steinerUnaryRoundPriorToRow,ih]

private theorem roundPrior_relabel (totals : List ℕ) :
    (encodeSteinerUnaryCappedRowTallies totals).map roundPriorSymbol = encodeSteinerUnaryRoundPriorVector totals := by
  induction totals with
  | nil => rfl
  | cons total totals ih =>
    change ((List.replicate total (Sum.inr (some true))++[Sum.inl true])++
      encodeSteinerUnaryCappedRowTallies totals).map roundPriorSymbol =
      (List.replicate total (Sum.inr (some true))++[Sum.inr none])++encodeSteinerUnaryRoundPriorVector totals
    simp only [List.map_append,List.map_replicate,List.map_singleton,roundPriorSymbol,ih]

/-- The actual run preserves all unary totals and produces their prior
frame in reverse, in one transition per symbol plus the final halt. -/
def steinerUnaryRoundPriorArchiveMachine_run (totals : List ℕ) :
    let input := encodeSteinerUnaryCappedRowTallies totals
    TM2OutputsInTime steinerUnaryRoundPriorArchiveMachine input
      (some (encodeSteinerUnaryRoundPriorVector totals).reverse) (input.length+1) := by
  have run := roundPrior_run (encodeSteinerUnaryCappedRowTallies totals) []
  rw [List.append_nil,roundPrior_relabel] at run
  change EvalsToInTime steinerUnaryRoundPriorArchiveMachine.step (initList _ _) (some (haltList _ _)) _
  rw [roundPrior_init,roundPrior_halt]
  exact run

/-- The unary cap appears once, ending in the bound marker. -/
def encodeSteinerUnaryRoundCap (n : ℕ) : List SteinerUnaryCappedRowsSymbol :=
  List.replicate n (Sum.inr (some true))++[Sum.inl false]

/-- Each distance row uses unary fields and a distinct row marker. -/
def encodeSteinerUnaryRoundDistances (rows : List (List ℕ)) : List SteinerUnaryCappedRowsSymbol :=
  rows.flatMap fun row => encodeSteinerUnaryRoundPriorVector row++[Sum.inl true]

private theorem roundPrior_frame_fields (values : List ℕ) :
    (values.flatMap fun value => List.replicate value (some true)++[none]).map
      (Sum.inr : Option Bool → RoundPriorSymbol) = encodeSteinerUnaryRoundPriorVector values := by
  induction values with
  | nil => rfl
  | cons value tail ih =>
    simp only [encodeSteinerUnaryRoundPriorVector,List.flatMap_cons,List.map_append,List.map_replicate,
      List.map_singleton,ih]

/-- Separate the three compact-round inputs for reuse between depths. -/
theorem encodeSteinerUnaryDistanceRound_components (request : SteinerUnaryDistanceRoundRequest) :
    encodeSteinerUnaryDistanceRound request =
      encodeSteinerUnaryRoundCap request.cap++encodeSteinerUnaryRoundPriorVector request.prior.toList++
        Sum.inl false::encodeSteinerUnaryRoundDistances (request.distances.map Vector.toList) := by
  let rows := request.distances.map Vector.toList
  let fields (row : List ℕ) := (row.flatMap fun value => List.replicate value (some true)++[none]).map
    (Sum.inr : Option Bool → RoundPriorSymbol)
  have same : fields = encodeSteinerUnaryRoundPriorVector := funext roundPrior_frame_fields
  change List.replicate request.cap (Sum.inr (some true))++Sum.inl false::
      (fields request.prior.toList++Sum.inl false::(rows.flatMap fun row => fields row++[Sum.inl true])) = _
  rw [same]
  simp only [encodeSteinerUnaryRoundCap,encodeSteinerUnaryRoundDistances,rows,List.append_assoc,List.cons_append,
    List.nil_append]

end OnlineReachabilityPreservers
