import OnlineReachabilityPreservers.SteinerUnaryDistanceHeightMachine
import OnlineReachabilityPreservers.SteinerUnaryRoundTotalMachine

/-! Run the two distance-table orientations and accumulate their exact scale. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev ScaleSymbol := SteinerUnaryCappedRowsSymbol
private abbrev ScaleHeightLabel := steinerUnaryDistanceHeightMachine.Λ
private abbrev ScaleHeightRegister := steinerUnaryDistanceHeightMachine.σ
private instance : Fintype ScaleHeightLabel := steinerUnaryDistanceHeightMachine.ΛFin

private inductive ScaleLabel where
  | readFirst | readSecond | restore (second : Bool)
  | rounds (second : Bool) (label : ScaleHeightLabel)
  | total (second : Bool) (label : PUnit)
  | finish
  deriving Fintype

private abbrev ScaleRegister := Option ScaleSymbol × ScaleHeightRegister
private abbrev ScaleProgram := StackMachineTag.Program (Fin 13) ScaleSymbol ScaleLabel ScaleRegister

private def scaleRegister (seen : Option ScaleSymbol) : ScaleRegister :=
  (seen,steinerUnaryDistanceHeightMachine.initialState)

private def scaleSeparator : ScaleSymbol := Sum.inr (some false)

private def scaleCurrentSymbol (r : ScaleRegister) : ScaleSymbol := r.1.getD scaleSeparator

private def scaleRead (slot : Fin 13) (code : ScaleProgram) : ScaleProgram :=
  pop slot (fun _ seen => scaleRegister seen) code

private def scaleGoto (label : ScaleLabel) : ScaleProgram :=
  load (fun _ => scaleRegister none) (goto fun _ => label)

private def scaleRestoreSlot : Bool → Fin 13
  | false => 0
  | true => 11

private def scaleRoundSlots : Fin 11 ↪ Fin 13 where
  toFun i := ⟨i.val,i.isLt.trans (by decide)⟩
  inj' := fun _ _ same => Fin.ext (congrArg (Fin.val : Fin 13 → ℕ) same)

private def scaleTotalSlots : Fin 2 ↪ Fin 13 where
  toFun := ![5,12]
  inj' := by intro a b same; fin_cases a <;> fin_cases b <;> simp_all

private def scaleRoundStart (second : Bool) : ScaleLabel := .rounds second steinerUnaryDistanceHeightMachine.main

private def scaleTotalStart (second : Bool) : ScaleLabel := .total second PUnit.unit

private def scaleTotalReturn : Bool → ScaleLabel
  | false => .restore true
  | true => .finish

private def scaleRoundTag (second : Bool) :
    StackMachineTag ScaleSymbol ScaleSymbol ScaleHeightLabel ScaleLabel ScaleHeightRegister ScaleRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (none,r)
  readRegister := Prod.snd
  writeLabel := .rounds second
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def scaleTotalTag (second : Bool) :
    StackMachineTag ScaleSymbol ScaleSymbol PUnit ScaleLabel (Option ScaleSymbol) ScaleRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister := scaleRegister
  readRegister := Prod.fst
  writeLabel := .total second
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def scaleRoundCode : ScaleLabel → StackMachineTag.Program (Fin 11) ScaleSymbol ScaleLabel ScaleRegister
  | .rounds second label => (scaleRoundTag second).returningStatement (scaleTotalStart second)
      (steinerUnaryDistanceHeightMachine.m label)
  | _ => halt

private def scaleTotalCode : ScaleLabel → StackMachineTag.Program (Fin 2) ScaleSymbol ScaleLabel ScaleRegister
  | .total second label => (scaleTotalTag second).returningStatement (scaleTotalReturn second)
      ((steinerUnaryRoundTotalMachine second).m label)
  | _ => halt

/- The two orientations use the same eleven active tapes in succession.
Slot 11 keeps the second request during the first run. Slot 12 holds
the accumulated unary scale from the live total machine. -/
private def scaleProgram : ScaleLabel → ScaleProgram
  | .readFirst => scaleRead 5 <| branch (fun r => scaleCurrentSymbol r == scaleSeparator)
      (scaleGoto .readSecond)
      (push 0 scaleCurrentSymbol (scaleGoto .readFirst))
  | .readSecond => scaleRead 5 <| branch (fun r => r.1.isSome)
      (push 11 scaleCurrentSymbol (scaleGoto .readSecond))
      (scaleGoto (.restore false))
  | .restore second => scaleRead (scaleRestoreSlot second) <| branch (fun r => r.1.isSome)
      (push 5 scaleCurrentSymbol (scaleGoto (.restore second)))
      (scaleGoto (scaleRoundStart second))
  | .rounds second label => StackIndexEmbedding.statement scaleRoundSlots (scaleRoundCode (.rounds second label))
  | .total second label => StackIndexEmbedding.statement scaleTotalSlots (scaleTotalCode (.total second label))
  | .finish => load (fun _ => scaleRegister none) halt

/-- Sum the exact rooted weights from both orientations and apply the
floor of one to the combined unary tally. -/
abbrev steinerUnaryForestScaleMachine : FinTM2 where
  K := Fin 13
  k₀ := 5
  k₁ := 12
  Γ _ := ScaleSymbol
  Λ := ScaleLabel
  main := .readFirst
  σ := ScaleRegister
  initialState := scaleRegister none
  m := scaleProgram

private def scaleTapes (work frame saved total : List ScaleSymbol) : Fin 13 → List ScaleSymbol :=
  ![work,[],[],[],[],frame,[],[],[],[],[],saved,total]

private def scaleCfg (label : Option ScaleLabel) (work frame saved total : List ScaleSymbol) :
    steinerUnaryForestScaleMachine.Cfg :=
  ⟨label,scaleRegister none,scaleTapes work frame saved total⟩

private theorem scaleUpdate0 (work frame saved total word : List ScaleSymbol) :
    Function.update (scaleTapes work frame saved total) 0 word = scaleTapes word frame saved total := by
  funext i
  fin_cases i <;> simp [scaleTapes,Function.update]

private theorem scaleUpdate5 (work frame saved total word : List ScaleSymbol) :
    Function.update (scaleTapes work frame saved total) 5 word = scaleTapes work word saved total := by
  funext i
  fin_cases i <;> simp [scaleTapes,Function.update]

private theorem scaleUpdate11 (work frame saved total word : List ScaleSymbol) :
    Function.update (scaleTapes work frame saved total) 11 word = scaleTapes work frame word total := by
  funext i
  fin_cases i <;> simp [scaleTapes,Function.update]

private theorem scaleUpdate12 (work frame saved total word : List ScaleSymbol) :
    Function.update (scaleTapes work frame saved total) 12 word = scaleTapes work frame saved word := by
  funext i
  fin_cases i <;> simp [scaleTapes,Function.update]

private abbrev ScaleRun (before after : steinerUnaryForestScaleMachine.Cfg) (bound : ℕ) :=
  EvalsToInTime steinerUnaryForestScaleMachine.step before (some after) bound

private def scaleOne {before after : steinerUnaryForestScaleMachine.Cfg}
    (move : steinerUnaryForestScaleMachine.step before = some after) : ScaleRun before after 1 :=
  ⟨⟨1,move⟩,le_rfl⟩

private def scaleThen {a b c : steinerUnaryForestScaleMachine.Cfg} {ta tb : ℕ}
    (first : ScaleRun a b ta) (second : ScaleRun b c tb) : ScaleRun a c (ta+tb) := by
  simpa only [Nat.add_comm] using EvalsToInTime.trans _ _ _ _ _ _ first second

private def scaleRelax {a b : steinerUnaryForestScaleMachine.Cfg} {small large : ℕ}
    (run : ScaleRun a b small) (le : small ≤ large) : ScaleRun a b large :=
  ⟨run.toEvalsTo,run.steps_le_m.trans le⟩

private theorem scaleFirst_push (symbol : ScaleSymbol) (different : symbol ≠ scaleSeparator)
    (word work : List ScaleSymbol) :
    steinerUnaryForestScaleMachine.step (scaleCfg (some .readFirst) work (symbol::word) [] []) =
      some (scaleCfg (some .readFirst) (symbol::work) word [] []) := by
  have check : (symbol == scaleSeparator) = false := by
    rcases symbol with b | (_ | b) <;> try rfl
    cases b
    · exact (different rfl).elim
    · rfl
  simp only [FinTM2.step,steinerUnaryForestScaleMachine,scaleCfg,Turing.TM2.step,Turing.TM2.stepAux,scaleProgram,
    scaleRead,scaleUpdate5,scaleUpdate0,scaleGoto,scaleCurrentSymbol]
  change some (bif symbol == scaleSeparator then scaleCfg (some .readSecond) work word [] []
    else scaleCfg (some .readFirst) (symbol::work) word [] []) = _
  rw [check]
  rfl

private theorem scaleFirst_end (word work : List ScaleSymbol) :
    steinerUnaryForestScaleMachine.step (scaleCfg (some .readFirst) work (scaleSeparator::word) [] []) =
      some (scaleCfg (some .readSecond) work word [] []) := by
  simp only [FinTM2.step,steinerUnaryForestScaleMachine,scaleCfg,Turing.TM2.step,Turing.TM2.stepAux,scaleProgram,
    scaleRead,scaleUpdate5,scaleGoto,scaleCurrentSymbol]
  rfl

private def scaleFirst (first second work : List ScaleSymbol) (clean : scaleSeparator ∉ first) :
    ScaleRun (scaleCfg (some .readFirst) work (first++scaleSeparator::second) [] [])
      (scaleCfg (some .readSecond) (first.reverse++work) second [] []) (first.length+1) := by
  induction first generalizing work with
  | nil => exact scaleOne (scaleFirst_end second work)
  | cons symbol first ih =>
    simp only [List.mem_cons,not_or] at clean
    have run := scaleThen (scaleOne (scaleFirst_push symbol (Ne.symm clean.1) _ work)) (ih (symbol::work) clean.2)
    simpa only [List.cons_append,List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,
      List.nil_append,Nat.add_left_comm,Nat.add_assoc] using run

private theorem scaleSecond_push (symbol : ScaleSymbol) (word work saved : List ScaleSymbol) :
    steinerUnaryForestScaleMachine.step (scaleCfg (some .readSecond) work (symbol::word) saved []) =
      some (scaleCfg (some .readSecond) work word (symbol::saved) []) := by
  simp only [FinTM2.step,steinerUnaryForestScaleMachine,scaleCfg,Turing.TM2.step,Turing.TM2.stepAux,scaleProgram,
    scaleRead,scaleUpdate5,scaleUpdate11,scaleGoto,scaleCurrentSymbol]
  rfl

private theorem scaleSecond_end (work saved : List ScaleSymbol) :
    steinerUnaryForestScaleMachine.step (scaleCfg (some .readSecond) work [] saved []) =
      some (scaleCfg (some (.restore false)) work [] saved []) := by
  simp only [FinTM2.step,steinerUnaryForestScaleMachine,scaleCfg,Turing.TM2.step,Turing.TM2.stepAux,scaleProgram,
    scaleRead,scaleUpdate5,scaleGoto]
  rfl

private def scaleSecond (second work saved : List ScaleSymbol) :
    ScaleRun (scaleCfg (some .readSecond) work second saved [])
      (scaleCfg (some (.restore false)) work [] (second.reverse++saved) []) (second.length+1) := by
  induction second generalizing saved with
  | nil => exact scaleOne (scaleSecond_end work saved)
  | cons symbol second ih =>
    have run := scaleThen (scaleOne (scaleSecond_push symbol second work saved)) (ih (symbol::saved))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_left_comm] using run

private def scaleRestoreCfg (label : ScaleLabel) : Bool →
    List ScaleSymbol → List ScaleSymbol → List ScaleSymbol → List ScaleSymbol → steinerUnaryForestScaleMachine.Cfg
  | false,source,frame,other,total => scaleCfg (some label) source frame other total
  | true,source,frame,other,total => scaleCfg (some label) other frame source total

private theorem scaleRestore_push (second : Bool) (symbol : ScaleSymbol) (source frame other total : List ScaleSymbol) :
    steinerUnaryForestScaleMachine.step (scaleRestoreCfg (.restore second) second (symbol::source) frame other total) =
      some (scaleRestoreCfg (.restore second) second source (symbol::frame) other total) := by
  cases second <;> simp only [scaleRestoreCfg,FinTM2.step,steinerUnaryForestScaleMachine,scaleCfg,Turing.TM2.step,
    Turing.TM2.stepAux,scaleProgram,scaleRead,scaleRestoreSlot,scaleUpdate0,scaleUpdate5,scaleUpdate11,scaleGoto,
    scaleCurrentSymbol] <;> rfl

private theorem scaleRestore_end (second : Bool) (frame other total : List ScaleSymbol) :
    steinerUnaryForestScaleMachine.step (scaleRestoreCfg (.restore second) second [] frame other total) =
      some (scaleRestoreCfg (scaleRoundStart second) second [] frame other total) := by
  cases second <;> simp only [scaleRestoreCfg,FinTM2.step,steinerUnaryForestScaleMachine,scaleCfg,Turing.TM2.step,
    Turing.TM2.stepAux,scaleProgram,scaleRead,scaleRestoreSlot,scaleUpdate0,scaleUpdate11,scaleGoto] <;> rfl

private def scaleRestore (second : Bool) (source frame other total : List ScaleSymbol) :
    ScaleRun (scaleRestoreCfg (.restore second) second source frame other total)
      (scaleRestoreCfg (scaleRoundStart second) second [] (source.reverse++frame) other total) (source.length+1) := by
  induction source generalizing frame with
  | nil => exact scaleOne (scaleRestore_end second frame other total)
  | cons symbol source ih =>
    have run := scaleThen (scaleOne (scaleRestore_push second symbol source frame other total)) (ih (symbol::frame))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_left_comm] using run

private theorem scaleFinish (total : List ScaleSymbol) :
    steinerUnaryForestScaleMachine.step (scaleCfg (some .finish) [] [] [] total) =
      some (scaleCfg none [] [] [] total) := rfl

private theorem scaleHostedTapes {k : ℕ} (slots : Fin k ↪ Fin 13)
    (active : Fin k → List ScaleSymbol) (extra expected : Fin 13 → List ScaleSymbol)
    (live : ∀ i, active i = expected (slots i)) (passive : ∀ i, (∀ j, slots j ≠ i) → extra i = expected i) :
    StackIndexEmbedding.tapesAt slots active extra = expected := by
  classical
  funext i
  by_cases found : ∃ j, slots j = i
  · obtain ⟨j,rfl⟩ := found
    rw [StackIndexEmbedding.tapesAt_image]
    exact live j
  · have outside (j) : slots j ≠ i := fun equal => found ⟨j,equal⟩
    rw [StackIndexEmbedding.tapesAt_extra slots _ _ outside]
    exact passive i outside

private noncomputable def scaleRoundsHosted (second : Bool) (saved total : List ScaleSymbol)
    (c : steinerUnaryDistanceHeightMachine.Cfg) : steinerUnaryForestScaleMachine.Cfg :=
  StackIndexEmbedding.configuration scaleRoundSlots (scaleTapes [] [] saved total)
    ((scaleRoundTag second).returningConfiguration (scaleTotalStart second) c)

private theorem scaleRoundsHosted_step (second : Bool) (saved total : List ScaleSymbol)
    {c after : steinerUnaryDistanceHeightMachine.Cfg} (move : steinerUnaryDistanceHeightMachine.step c = some after) :
    steinerUnaryForestScaleMachine.step (scaleRoundsHosted second saved total c) =
      some (scaleRoundsHosted second saved total after) := by
  have tagged := (scaleRoundTag second).step_embedded_return (scaleTotalStart second)
    (base := steinerUnaryDistanceHeightMachine.m) (host := scaleRoundCode) (fun _ => rfl) move
  have hosted := StackIndexEmbedding.step_on scaleRoundSlots (base := scaleRoundCode)
    (scaleTapes [] [] saved total) ((scaleRoundTag second).returningConfiguration (scaleTotalStart second) c)
  rw [tagged] at hosted
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact hosted

private theorem scaleRoundsHosted_tapes (second : Bool) (word saved total : List ScaleSymbol)
    (c : steinerUnaryDistanceHeightMachine.Cfg) (shape : c.stk = ![[],[],[],[],[],word,[],[],[],[],[]]) :
    (scaleRoundsHosted second saved total c).stk = scaleTapes [] word saved total := by
  change StackIndexEmbedding.tapesAt scaleRoundSlots (fun i => (c.stk i).map id) (scaleTapes [] [] saved total) = _
  apply scaleHostedTapes
  · intro i
    rw [List.map_id,shape]
    fin_cases i <;> rfl
  · intro i outside
    have different : i ≠ 5 := fun same => outside 5 same.symm
    have changed := congrFun (scaleUpdate5 [] [] saved total word) i
    rw [Function.update_of_ne different] at changed
    exact changed

private theorem scaleRoundsHosted_init (second : Bool) (word saved total : List ScaleSymbol) :
    scaleRoundsHosted second saved total (initList steinerUnaryDistanceHeightMachine word) =
      scaleCfg (some (scaleRoundStart second)) [] word saved total := by
  apply congrArg (fun tapes : Fin 13 → List ScaleSymbol =>
    (⟨some (scaleRoundStart second),scaleRegister none,tapes⟩ : steinerUnaryForestScaleMachine.Cfg))
  apply scaleRoundsHosted_tapes
  funext i
  fin_cases i <;> rfl

private theorem scaleRoundsHosted_halt (second : Bool) (word saved total : List ScaleSymbol) :
    scaleRoundsHosted second saved total (haltList steinerUnaryDistanceHeightMachine word) =
      scaleCfg (some (scaleTotalStart second)) [] word saved total := by
  apply congrArg (fun tapes : Fin 13 → List ScaleSymbol =>
    (⟨some (scaleTotalStart second),scaleRegister none,tapes⟩ : steinerUnaryForestScaleMachine.Cfg))
  apply scaleRoundsHosted_tapes
  funext i
  fin_cases i <;> rfl

private noncomputable def scaleHeightPolynomial (height : ℕ) : Polynomial ℕ :=
  (steinerUnaryDistanceHeightMachine_polytime height).time

private noncomputable def scaleRoundsRun {n : ℕ} (second : Bool) (dist : Fin n × Fin n → ℕ)
    (height : ℕ) (saved total : List ScaleSymbol) :
    let input := encodeSteinerUnaryDistanceHeight dist height
    let output := encodeSteinerUnaryCappedRowTallies (inwardHeightWeightRounds dist height).toList
    ScaleRun (scaleCfg (some (scaleRoundStart second)) [] input saved total)
      (scaleCfg (some (scaleTotalStart second)) [] output saved total) ((scaleHeightPolynomial height).eval input.length) := by
  let certificate := steinerUnaryDistanceHeightMachine_polytime height
  let run : TM2OutputsInTime steinerUnaryDistanceHeightMachine (encodeSteinerUnaryDistanceHeight dist height)
      (some (encodeSteinerUnaryCappedRowTallies (inwardHeightWeightRounds dist height).toList))
      ((scaleHeightPolynomial height).eval (encodeSteinerUnaryDistanceHeight dist height).length) := by
    have typed := certificate.outputsFun ⟨n,dist⟩
    change TM2OutputsInTime steinerUnaryDistanceHeightMachine ((encodeSteinerUnaryDistanceHeight dist height).map id)
      (some ((encodeSteinerUnaryCappedRowTallies (inwardHeightWeightRounds dist height).toList).map id))
      ((scaleHeightPolynomial height).eval (encodeSteinerUnaryDistanceHeight dist height).length) at typed
    simpa only [List.map_id] using typed
  have hosted := iterate_map_some (scaleRoundsHosted second saved total)
    (fun move => scaleRoundsHosted_step second saved total move) run.steps run.evals_in_steps
  rw [scaleRoundsHosted_init,scaleRoundsHosted_halt] at hosted
  exact ⟨⟨run.steps,hosted⟩,run.steps_le_m⟩

private noncomputable def scaleTotalHosted (second : Bool) (saved : List ScaleSymbol)
    (c : (steinerUnaryRoundTotalMachine second).Cfg) : steinerUnaryForestScaleMachine.Cfg :=
  StackIndexEmbedding.configuration scaleTotalSlots (scaleTapes [] [] saved [])
    ((scaleTotalTag second).returningConfiguration (scaleTotalReturn second) c)

private theorem scaleTotalHosted_step (second : Bool) (saved : List ScaleSymbol)
    {c after : (steinerUnaryRoundTotalMachine second).Cfg} (move : (steinerUnaryRoundTotalMachine second).step c = some after) :
    steinerUnaryForestScaleMachine.step (scaleTotalHosted second saved c) = some (scaleTotalHosted second saved after) := by
  have tagged := (scaleTotalTag second).step_embedded_return (scaleTotalReturn second)
    (base := (steinerUnaryRoundTotalMachine second).m) (host := scaleTotalCode) (fun _ => rfl) move
  have hosted := StackIndexEmbedding.step_on scaleTotalSlots (base := scaleTotalCode)
    (scaleTapes [] [] saved []) ((scaleTotalTag second).returningConfiguration (scaleTotalReturn second) c)
  rw [tagged] at hosted
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact hosted

private theorem scaleTotalHosted_tapes (second : Bool) (word saved total : List ScaleSymbol)
    (c : (steinerUnaryRoundTotalMachine second).Cfg) (shape : c.stk = ![word,total]) :
    (scaleTotalHosted second saved c).stk = scaleTapes [] word saved total := by
  change StackIndexEmbedding.tapesAt scaleTotalSlots (fun i => (c.stk i).map id) (scaleTapes [] [] saved []) = _
  apply scaleHostedTapes
  · intro i
    rw [List.map_id,shape]
    fin_cases i <;> rfl
  · intro i outside
    have different5 : i ≠ 5 := fun same => outside 0 same.symm
    have different12 : i ≠ 12 := fun same => outside 1 same.symm
    have same5 := congrFun (scaleUpdate5 [] [] saved [] word) i
    have same12 := congrFun (scaleUpdate12 [] word saved [] total) i
    rw [Function.update_of_ne different5] at same5
    rw [Function.update_of_ne different12] at same12
    exact same5.trans same12

private theorem scaleTotalHosted_init (second : Bool) (word saved : List ScaleSymbol) (total : ℕ) :
    scaleTotalHosted second saved (steinerUnaryRoundTotalCfg second (some PUnit.unit) word total) =
      scaleCfg (some (scaleTotalStart second)) [] word saved (encodeSteinerUnaryRoundTotal total) := by
  apply congrArg (fun tapes : Fin 13 → List ScaleSymbol =>
    (⟨some (scaleTotalStart second),scaleRegister none,tapes⟩ : steinerUnaryForestScaleMachine.Cfg))
  exact scaleTotalHosted_tapes second word saved (encodeSteinerUnaryRoundTotal total) _ rfl

private theorem scaleTotalHosted_halt (second : Bool) (saved : List ScaleSymbol) (total : ℕ) :
    scaleTotalHosted second saved (steinerUnaryRoundTotalCfg second none [] total) =
      scaleCfg (some (scaleTotalReturn second)) [] [] saved (encodeSteinerUnaryRoundTotal total) := by
  apply congrArg (fun tapes : Fin 13 → List ScaleSymbol =>
    (⟨some (scaleTotalReturn second),scaleRegister none,tapes⟩ : steinerUnaryForestScaleMachine.Cfg))
  exact scaleTotalHosted_tapes second [] saved (encodeSteinerUnaryRoundTotal total) _ rfl

private noncomputable def scaleTotalRun (second : Bool) (saved : List ScaleSymbol) (values : List ℕ) (prior : ℕ) :
    let input := encodeSteinerUnaryCappedRowTallies values
    let total := prior+values.sum
    ScaleRun (scaleCfg (some (scaleTotalStart second)) [] input saved (encodeSteinerUnaryRoundTotal prior))
      (scaleCfg (some (scaleTotalReturn second)) [] [] saved
        (encodeSteinerUnaryRoundTotal (if second then max 1 total else total))) (input.length+1) := by
  let run := steinerUnaryRoundTotalMachine_run second values prior
  have hosted := iterate_map_some (scaleTotalHosted second saved)
    (fun move => scaleTotalHosted_step second saved move) run.steps run.evals_in_steps
  rw [scaleTotalHosted_init,scaleTotalHosted_halt] at hosted
  exact ⟨⟨run.steps,hosted⟩,run.steps_le_m⟩

private theorem scalePrior_no_separator (values : List ℕ) : scaleSeparator ∉ encodeSteinerUnaryRoundPriorVector values := by
  simp [encodeSteinerUnaryRoundPriorVector,scaleSeparator,List.mem_flatMap,List.mem_replicate]

private theorem scaleRows_no_separator (rows : List (List ℕ)) : scaleSeparator ∉ encodeSteinerUnaryRoundDistances rows := by
  induction rows with
  | nil => simp [encodeSteinerUnaryRoundDistances]
  | cons row rows ih =>
    have prior := scalePrior_no_separator row
    simp only [encodeSteinerUnaryRoundDistances,List.flatMap_cons,List.mem_append,not_or]
    refine ⟨⟨prior,by simp [scaleSeparator]⟩,?_⟩
    exact ih

private theorem scaleHeight_no_separator {n : ℕ} (dist : Fin n × Fin n → ℕ) (height : ℕ) :
    scaleSeparator ∉ encodeSteinerUnaryDistanceHeight dist height := by
  change scaleSeparator ∉ List.replicate height (Sum.inr (some true)) ++
    Sum.inl false :: (encodeSteinerUnaryRoundCap n ++ encodeSteinerUnaryRoundDistances
      (List.ofFn fun root => List.ofFn fun child => dist (child,root)))
  have table := scaleRows_no_separator (List.ofFn fun root => List.ofFn fun child => dist (child,root))
  simp only [encodeSteinerUnaryRoundCap,List.mem_append,List.mem_replicate,List.mem_cons,List.not_mem_nil,
    or_false,not_or]
  refine ⟨fun h => ?_,fun h => ?_,⟨fun h => ?_,fun h => ?_⟩,table⟩
  all_goals simp [scaleSeparator] at h

/-- Supply the same distance data in the two transfer orders. -/
def encodeSteinerUnaryForestScaleInput {n : ℕ} (dist : Fin n × Fin n → ℕ) (height : ℕ) :
    List SteinerUnaryCappedRowsSymbol :=
  encodeSteinerUnaryDistanceHeight dist height ++
    scaleSeparator :: encodeSteinerUnaryDistanceHeight (fun d => dist d.swap) height

private theorem scaleInput_length {n : ℕ} (dist : Fin n × Fin n → ℕ) (height : ℕ) :
    (encodeSteinerUnaryForestScaleInput dist height).length =
      (encodeSteinerUnaryDistanceHeight dist height).length+
      (encodeSteinerUnaryDistanceHeight (fun d => dist d.swap) height).length+1 := by
  simp only [encodeSteinerUnaryForestScaleInput,List.length_append,List.length_cons]
  omega

private theorem scaleInput_cap_le {n : ℕ} (dist : Fin n × Fin n → ℕ) (height : ℕ) :
    n+1 ≤ (encodeSteinerUnaryDistanceHeight dist height).length := by
  simp only [encodeSteinerUnaryDistanceHeight,encodeSteinerUnaryRoundCap,List.length_append,List.length_cons,
    List.length_replicate]
  omega

private theorem scaleInit (word : List ScaleSymbol) :
    initList steinerUnaryForestScaleMachine word = scaleCfg (some .readFirst) [] word [] [] := by
  apply congrArg (fun tapes : Fin 13 → List ScaleSymbol =>
    (⟨some .readFirst,scaleRegister none,tapes⟩ : steinerUnaryForestScaleMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem scaleHalt (word : List ScaleSymbol) :
    haltList steinerUnaryForestScaleMachine word = scaleCfg none [] [] [] word := by
  apply congrArg (fun tapes : Fin 13 → List ScaleSymbol =>
    (⟨none,scaleRegister none,tapes⟩ : steinerUnaryForestScaleMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private def scaleRowLimit (height X : ℕ) : ℕ := X*(X^(height+1)+1)

private theorem scaleRowBound {n : ℕ} (dist : Fin n × Fin n → ℕ) (height : ℕ) {X : ℕ}
    (cap_le : n+1 ≤ X) :
    (encodeSteinerUnaryCappedRowTallies (inwardHeightWeightRounds dist height).toList).length ≤ scaleRowLimit height X := by
  let values := inwardHeightWeightRounds dist height
  have length := encodeSteinerUnaryRoundPriorVector_length_le values (inwardHeightWeightRounds_get_le dist height)
  have same := congrArg List.length (encodeSteinerUnaryRoundPriorVector_map_toRows values.toList)
  rw [List.length_map] at same
  have budget : inwardHeightWeightRoundBound n height ≤ X^(height+1) :=
    ((Nat.le_add_right _ _).trans (inwardHeightWeightRoundBound_add_le n height)).trans
      (Nat.pow_le_pow_left cap_le _)
  rw [← same]
  exact length.trans (Nat.mul_le_mul (by omega) (Nat.add_le_add_right budget 1))

private theorem scalePoly_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro x y le
  change p.eval x ≤ p.eval y
  rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum,Polynomial.sum_def,Polynomial.sum_def]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left le _)

/-- Actual two-orientation running-time bound as a polynomial in the
length of the supplied frame at fixed height. -/
noncomputable def steinerUnaryForestScalePolynomial (height : ℕ) : Polynomial ℕ :=
  let X : Polynomial ℕ := Polynomial.X
  Polynomial.C 2*X+Polynomial.C 2*scaleHeightPolynomial height+
    Polynomial.C 2*(X*(X^(height+1)+Polynomial.C 1))+Polynomial.C 5

/-- Compute both rooted vectors on live tapes and emit the exact
positive scale for a supplied table. -/
noncomputable def steinerUnaryForestScaleMachine_run {n : ℕ} (dist : Fin n × Fin n → ℕ) (height : ℕ) :
    let input := encodeSteinerUnaryForestScaleInput dist height
    TM2OutputsInTime steinerUnaryForestScaleMachine input
      (some (encodeSteinerUnaryRoundTotal (forestScaleFromDistanceRounds dist height)))
      ((steinerUnaryForestScalePolynomial height).eval input.length) := by
  let input := encodeSteinerUnaryForestScaleInput dist height
  let reverse : Fin n × Fin n → ℕ := fun d => dist d.swap
  let first := encodeSteinerUnaryDistanceHeight dist height
  let second := encodeSteinerUnaryDistanceHeight reverse height
  let firstValues := (inwardHeightWeightRounds dist height).toList
  let secondValues := (inwardHeightWeightRounds reverse height).toList
  let X := input.length
  have fullLength : X = first.length+second.length+1 := scaleInput_length dist height
  have firstAvailable : first.length ≤ X := by omega
  have cap : n+1 ≤ X := (scaleInput_cap_le dist height).trans firstAvailable
  have firstTime := scalePoly_mono (scaleHeightPolynomial height) firstAvailable
  have secondTime := scalePoly_mono (scaleHeightPolynomial height) (show second.length ≤ X by omega)
  have firstLen := scaleRowBound dist height cap
  have secondLen := scaleRowBound reverse height cap
  have read1 := scaleFirst first second [] (scaleHeight_no_separator dist height)
  rw [List.append_nil] at read1
  have read2 := scaleSecond second first.reverse []
  rw [List.append_nil] at read2
  have load1 := scaleRestore false first.reverse [] second.reverse []
  simp only [scaleRestoreCfg,List.reverse_reverse,List.append_nil,List.length_reverse] at load1
  have run1 := scaleRoundsRun false dist height second.reverse []
  dsimp only at run1
  have add1 := scaleTotalRun false second.reverse firstValues 0
  have zeroTotal : encodeSteinerUnaryRoundTotal 0 = [] := rfl
  simp only [scaleTotalReturn,Bool.false_eq_true,ite_false,Nat.zero_add,zeroTotal] at add1
  let accumulated := encodeSteinerUnaryRoundTotal firstValues.sum
  have load2 := scaleRestore true second.reverse [] [] accumulated
  simp only [scaleRestoreCfg,List.reverse_reverse,List.append_nil,List.length_reverse] at load2
  have run2 := scaleRoundsRun true reverse height [] accumulated
  dsimp only at run2
  have add2 := scaleTotalRun true [] secondValues firstValues.sum
  simp only [scaleTotalReturn,ite_true] at add2
  have result : forestScaleFromDistanceRounds dist height = max 1 (firstValues.sum+secondValues.sum) :=
    forestScaleFromDistanceRounds_eq_vectorTotals dist height
  rw [← result] at add2
  have done := scaleOne (scaleFinish (encodeSteinerUnaryRoundTotal (forestScaleFromDistanceRounds dist height)))
  have read := scaleThen read1 read2
  have firstRound := scaleThen load1 run1
  have firstTotal := scaleThen firstRound add1
  have secondRound := scaleThen load2 run2
  have secondTotal := scaleThen secondRound add2
  have run := scaleThen (scaleThen (scaleThen read firstTotal) secondTotal) done
  change ScaleRun (initList steinerUnaryForestScaleMachine input) (haltList steinerUnaryForestScaleMachine _) _
  rw [scaleInit,scaleHalt]
  refine scaleRelax run ?_
  simp only [steinerUnaryForestScalePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow]
  change _ ≤ 2*X+2*(scaleHeightPolynomial height).eval X+2*scaleRowLimit height X+5
  dsimp only [first,second,firstValues,secondValues] at fullLength firstTime secondTime ⊢
  omega

/-- Native fixed-height polynomial certificate for the two supplied
orientations, including the positive floor. -/
noncomputable def steinerUnaryForestScaleMachine_polytime (height : ℕ) :
    TM2ComputableInPolyTime
      (fun request : Σ n : ℕ, (Fin n × Fin n → ℕ) => encodeSteinerUnaryForestScaleInput request.2 height)
      encodeSteinerUnaryRoundTotal (fun request => forestScaleFromDistanceRounds request.2 height) where
  tm := steinerUnaryForestScaleMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := steinerUnaryForestScalePolynomial height
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq] using steinerUnaryForestScaleMachine_run request.2 height

/-- A supplied exact hop table yields the priced height-forest scale. -/
noncomputable def steinerUnaryForestScaleMachine_hops {n : ℕ} (G : Arcs (Fin n)) (height : ℕ) :
    let dist : Fin n × Fin n → ℕ := fun d => hops G d.1 d.2
    let input := encodeSteinerUnaryForestScaleInput dist height
    TM2OutputsInTime steinerUnaryForestScaleMachine input (some (encodeSteinerUnaryRoundTotal (forestScale G height)))
      ((steinerUnaryForestScalePolynomial height).eval input.length) := by
  let dist : Fin n × Fin n → ℕ := fun d => hops G d.1 d.2
  simpa only [forestScaleFromDistanceRounds_eq G dist (fun _ => rfl)] using steinerUnaryForestScaleMachine_run dist height

end OnlineReachabilityPreservers
