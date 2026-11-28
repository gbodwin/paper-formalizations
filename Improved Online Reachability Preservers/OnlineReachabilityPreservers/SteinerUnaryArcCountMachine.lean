import OnlineReachabilityPreservers.SteinerUnaryArcTableMachine

/-! Count the true entries of the checked unary arc table. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev ArcTableLabel := steinerUnaryArcTableMachine.Λ
private abbrev ArcTableRegister := steinerUnaryArcTableMachine.σ
private instance : Fintype ArcTableLabel := steinerUnaryArcTableMachine.ΛFin

private inductive ArcCountLabel where
  | table (label : ArcTableLabel)
  | tally
  | finish
  deriving Fintype

private abbrev ArcCountRegister := Option (Option Bool) × ArcTableRegister
private abbrev ArcCountProgram := StackMachineTag.Program (Fin 8) (Option Bool) ArcCountLabel ArcCountRegister

private def arcCountInitial : ArcCountRegister := (none,steinerUnaryArcTableMachine.initialState)

private def arcCountObserve (_ : ArcCountRegister) (seen : Option (Option Bool)) : ArcCountRegister :=
  (seen,steinerUnaryArcTableMachine.initialState)

private def arcCountNext (label : ArcCountLabel) : ArcCountProgram :=
  load (fun _ => arcCountInitial) (goto (fun _ => label))

private def arcCountTag :
    StackMachineTag (Option Bool) (Option Bool) ArcTableLabel ArcCountLabel ArcTableRegister ArcCountRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (none,r)
  readRegister := Prod.snd
  writeLabel := .table
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def arcCountProgram : ArcCountLabel → ArcCountProgram
  | .table label => arcCountTag.returningStatement .tally (steinerUnaryArcTableMachine.m label)
  | .tally =>
    pop 4 arcCountObserve <|
      branch (fun r => r.1.isSome)
        (branch (fun r => r.1 == some (some true))
          (push 0 (fun _ => some true) (arcCountNext .tally)) (arcCountNext .tally))
        (arcCountNext .finish)
  | .finish =>
    pop 0 arcCountObserve <|
      branch (fun r => r.1.isSome)
        (push 4 (fun _ => some true) (arcCountNext .finish))
        (load (fun _ => arcCountInitial) halt)

/-- Run the ordered arc table and then count only the true entries. -/
abbrev steinerUnaryArcCountMachine : FinTM2 where
  K := Fin 8
  k₀ := 4
  k₁ := 4
  Γ _ := Option Bool
  Λ := ArcCountLabel
  main := .table steinerUnaryArcTableMachine.main
  σ := ArcCountRegister
  initialState := arcCountInitial
  m := arcCountProgram

private abbrev countTallies (n : ℕ) : List (Option Bool) := List.replicate n (some true)

private def arcCountCfg (label : Option ArcCountLabel) (paid : ℕ) (word : List (Option Bool)) :
    steinerUnaryArcCountMachine.Cfg where
  l := label
  var := arcCountInitial
  stk := ![countTallies paid,[],[],[],word,[],[],[]]

private theorem arcCount_update4 (tallies word next : List (Option Bool)) :
    Function.update (![tallies,[],[],[],word,[],[],[]] : Fin 8 → List (Option Bool)) 4 next =
      ![tallies,[],[],[],next,[],[],[]] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem arcCount_update0 (tallies word next : List (Option Bool)) :
    Function.update (![tallies,[],[],[],word,[],[],[]] : Fin 8 → List (Option Bool)) 0 next =
      ![next,[],[],[],word,[],[],[]] := by
  funext i
  fin_cases i <;> simp [Function.update]

private def arcCount_one {a b : steinerUnaryArcCountMachine.Cfg} (step : steinerUnaryArcCountMachine.step a = some b) :
    EvalsToInTime steinerUnaryArcCountMachine.step a (some b) 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := step

private theorem arcCount_read (symbol : Option Bool) (word : List (Option Bool)) (paid : ℕ) :
    steinerUnaryArcCountMachine.step (arcCountCfg (some .tally) paid (symbol::word)) =
      some (arcCountCfg (some .tally) (paid+if symbol = some true then 1 else 0) word) := by
  cases symbol with
  | none =>
    simp [FinTM2.step,steinerUnaryArcCountMachine,arcCountCfg,Turing.TM2.step,Turing.TM2.stepAux,
      arcCountProgram,arcCountObserve,arcCountNext,arcCount_update4]
    rfl
  | some b =>
    cases b <;> simp [FinTM2.step,steinerUnaryArcCountMachine,arcCountCfg,Turing.TM2.step,Turing.TM2.stepAux,
      arcCountProgram,arcCountObserve,arcCountNext,arcCount_update0,arcCount_update4,List.replicate_succ] <;> rfl

private theorem arcCount_tallyEnd (paid : ℕ) :
    steinerUnaryArcCountMachine.step (arcCountCfg (some .tally) paid []) =
      some (arcCountCfg (some .finish) paid []) := by
  simp [FinTM2.step,steinerUnaryArcCountMachine,arcCountCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcCountProgram,arcCountObserve,arcCountNext,arcCount_update4]
  rfl

private def arcCount_scan (word : List (Option Bool)) (paid : ℕ) :
    EvalsToInTime steinerUnaryArcCountMachine.step
      (arcCountCfg (some .tally) paid word)
      (some (arcCountCfg (some .finish) (paid+word.count (some true)) [])) (word.length+1) := by
  induction word generalizing paid with
  | nil => exact arcCount_one (arcCount_tallyEnd paid)
  | cons symbol word ih =>
    have first := arcCount_one (arcCount_read symbol word paid)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (paid+if symbol = some true then 1 else 0))
    have count : paid+(if symbol = some true then 1 else 0)+word.count (some true) =
        paid+(symbol::word).count (some true) := by
      rw [List.count_cons]
      simp only [beq_iff_eq]
      omega
    simpa only [count,List.length_cons] using all

private theorem arcCount_output (paid : ℕ) (word : List (Option Bool)) :
    steinerUnaryArcCountMachine.step (arcCountCfg (some .finish) (paid+1) word) =
      some (arcCountCfg (some .finish) paid (some true::word)) := by
  simp [FinTM2.step,steinerUnaryArcCountMachine,arcCountCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcCountProgram,arcCountObserve,arcCountNext,arcCount_update0,arcCount_update4,List.replicate_succ]
  rfl

private theorem arcCount_finishEnd (word : List (Option Bool)) :
    steinerUnaryArcCountMachine.step (arcCountCfg (some .finish) 0 word) =
      some (arcCountCfg none 0 word) := by
  simp [FinTM2.step,steinerUnaryArcCountMachine,arcCountCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcCountProgram,arcCountObserve,arcCount_update0]
  rfl

private def arcCount_finish (paid : ℕ) (word : List (Option Bool)) :
    EvalsToInTime steinerUnaryArcCountMachine.step
      (arcCountCfg (some .finish) paid word)
      (some (arcCountCfg none 0 (countTallies paid++word))) (paid+1) := by
  induction paid generalizing word with
  | zero => exact arcCount_one (arcCount_finishEnd word)
  | succ paid ih =>
    have first := arcCount_one (arcCount_output paid word)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (some true::word))
    have order : countTallies paid++some true::word = countTallies (paid+1)++word := by
      simp only [List.replicate_add,List.replicate_one,List.append_assoc,List.singleton_append]
    rw [order] at all
    exact all

private theorem arcCount_liftInit (frame : List (Option Bool)) :
    arcCountTag.returningConfiguration .tally (initList steinerUnaryArcTableMachine frame) =
      initList steinerUnaryArcCountMachine frame := by
  apply congrArg (fun stk : Fin 8 → List (Option Bool) =>
    (⟨some (.table steinerUnaryArcTableMachine.main),arcCountInitial,stk⟩ : steinerUnaryArcCountMachine.Cfg))
  funext i
  change ((initList steinerUnaryArcTableMachine frame).stk i).map id = (initList steinerUnaryArcCountMachine frame).stk i
  rw [List.map_id]
  rfl

private theorem arcCount_liftReturn (word : List (Option Bool)) :
    arcCountTag.returningConfiguration .tally (haltList steinerUnaryArcTableMachine word) =
      arcCountCfg (some .tally) 0 word := by
  apply congrArg (fun stk : Fin 8 → List (Option Bool) =>
    (⟨some .tally,arcCountInitial,stk⟩ : steinerUnaryArcCountMachine.Cfg))
  funext i
  change ((haltList steinerUnaryArcTableMachine word).stk i).map id = (arcCountCfg (some .tally) 0 word).stk i
  rw [List.map_id]
  fin_cases i <;> rfl

private theorem arcCount_halt (word : List (Option Bool)) :
    haltList steinerUnaryArcCountMachine word = arcCountCfg none 0 word := by
  apply congrArg (fun stk : Fin 8 → List (Option Bool) => (⟨none,arcCountInitial,stk⟩ : steinerUnaryArcCountMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private def arcCount_tableAndTally {time : ℕ} (frame word : List (Option Bool))
    (run : TM2OutputsInTime steinerUnaryArcTableMachine frame (some word) time) :
    TM2OutputsInTime steinerUnaryArcCountMachine frame (some (countTallies (word.count (some true))))
      (time+word.length+word.count (some true)+2) := by
  have evaluated := arcCountTag.evaluationReturning .tally (base := steinerUnaryArcTableMachine.m)
    (host := arcCountProgram) (fun _ => rfl) run
  change EvalsToInTime steinerUnaryArcCountMachine.step
    (arcCountTag.returningConfiguration .tally (initList steinerUnaryArcTableMachine frame))
    (some (arcCountTag.returningConfiguration .tally (haltList steinerUnaryArcTableMachine word))) time at evaluated
  rw [arcCount_liftInit,arcCount_liftReturn] at evaluated
  have counted := arcCount_scan word 0
  rw [Nat.zero_add] at counted
  have written := arcCount_finish (word.count (some true)) []
  rw [List.append_nil] at written
  have all := EvalsToInTime.trans _ _ _ _ _ _ (EvalsToInTime.trans _ _ _ _ _ _ evaluated counted) written
  change EvalsToInTime steinerUnaryArcCountMachine.step _ (some (haltList steinerUnaryArcCountMachine _)) _
  rw [arcCount_halt]
  exact ⟨all.toEvalsTo,by have spent := all.steps_le_m; omega⟩

/-- Count the supplied queries that occur in the graph. Repeated query
names contribute once per occurrence. -/
def steinerUnaryArcCount (request : SteinerUnaryArcTable) : ℕ :=
  (steinerUnaryArcTableAnswer request).count (some true)

/-- The machine returns one true unary tally per qualifying query. -/
def steinerUnaryArcCountAnswer (request : SteinerUnaryArcTable) : List (Option Bool) :=
  List.replicate (steinerUnaryArcCount request) (some true)

theorem steinerUnaryArcCount_eq_filter (request : SteinerUnaryArcTable) :
    steinerUnaryArcCount request = (request.2.filter fun arc => decide (arc ∈ request.1)).length := by
  simp [steinerUnaryArcCount,steinerUnaryArcTableAnswer,List.count_eq_length_filter,List.filter_map,Function.comp_def]

private theorem arcCount_table_length (request : SteinerUnaryArcTable) :
    (steinerUnaryArcTableAnswer request).length = request.2.length := by
  simp only [steinerUnaryArcTableAnswer,List.length_map]

/-- The table pass uses its existing bound. The final tally adds one
transition per table entry, one per true entry, and two more transitions. -/
def steinerUnaryArcCountMachine_run (request : SteinerUnaryArcTable) :
    let G := (encodeSteinerUnaryArcRows request.1).length
    let Q := (encodeSteinerUnaryArcRows request.2).length
    let q := request.2.length
    TM2OutputsInTime steinerUnaryArcCountMachine (encodeSteinerUnaryArcTable request)
      (some (steinerUnaryArcCountAnswer request)) (2*G+5*Q+(5*G+8)*q+steinerUnaryArcCount request+6) := by
  have all := arcCount_tableAndTally _ _ (steinerUnaryArcTableMachine_run request)
  have cost := all.steps_le_m
  simp only [arcCount_table_length] at cost
  refine ⟨all.toEvalsTo,?_⟩
  dsimp only
  simp only [Nat.add_mul,steinerUnaryArcCount] at cost ⊢
  omega

/-- The whole count is quadratic in the actual graph and query frame. -/
def steinerUnaryArcCountMachine_quadratic (request : SteinerUnaryArcTable) :
    let X := (encodeSteinerUnaryArcTable request).length
    TM2OutputsInTime steinerUnaryArcCountMachine (encodeSteinerUnaryArcTable request)
      (some (steinerUnaryArcCountAnswer request)) (5*X^2+16*X+6) := by
  dsimp only
  let X := (encodeSteinerUnaryArcTable request).length
  have qFits : request.2.length ≤ X := by
    have length := steinerUnaryArcRows_count_le_frame request.2
    dsimp only [X,encodeSteinerUnaryArcTable]
    simp only [List.length_append,List.length_cons]
    omega
  let word := steinerUnaryArcTableAnswer request
  have countFits : word.count (some true) ≤ word.length := List.count_le_length
  have tableSize : word.length = request.2.length := arcCount_table_length request
  have all := arcCount_tableAndTally _ word (steinerUnaryArcTableMachine_quadratic request)
  refine ⟨all.toEvalsTo,all.steps_le_m.trans ?_⟩
  change 5*X^2+14*X+4+word.length+word.count (some true)+2 ≤ 5*X^2+16*X+6
  omega

/-- This polynomial bounds the actual table and tally machine. -/
noncomputable def steinerUnaryArcCountMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryArcTable id steinerUnaryArcCountAnswer where
  tm := steinerUnaryArcCountMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 5*Polynomial.X^2+Polynomial.C 16*Polynomial.X+Polynomial.C 6
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,
      Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_pow] using steinerUnaryArcCountMachine_quadratic request

/-- The numeric query values count exactly the finite queries in the graph. -/
theorem steinerUnaryArcCount_finite_queries {n : ℕ} (rows queries : List (Fin n × Fin n)) :
    steinerUnaryArcCount (rows.map steinerUnaryArcValues,queries.map steinerUnaryArcValues) =
      (queries.filter fun arc => decide (arc ∈ rows.toFinset)).length := by
  rw [steinerUnaryArcCount_eq_filter]
  change ((queries.map steinerUnaryArcValues).filter fun arc => decide (arc ∈ rows.map steinerUnaryArcValues)).length = _
  rw [List.filter_map,List.length_map]
  apply congrArg List.length
  apply List.filter_congr
  intro arc _
  change decide (steinerUnaryArcValues arc ∈ rows.map steinerUnaryArcValues) = decide (arc ∈ rows.toFinset)
  simp only [steinerUnaryArcValues_mem_finset]

/-- When the supplied candidate list is duplicate-free and includes the
graph, the tally is the cardinality of the graph's finite arc set. -/
def steinerUnaryArcCountMachine_finset {n : ℕ} (rows queries : List (Fin n × Fin n))
    (unique : queries.Nodup) (covers : rows.toFinset ⊆ queries.toFinset) :
    let request : SteinerUnaryArcTable := (rows.map steinerUnaryArcValues,queries.map steinerUnaryArcValues)
    let X := (encodeSteinerUnaryArcTable request).length
    TM2OutputsInTime steinerUnaryArcCountMachine (encodeSteinerUnaryArcTable request)
      (some (List.replicate rows.toFinset.card (some true))) (5*X^2+16*X+6) := by
  let request : SteinerUnaryArcTable := (rows.map steinerUnaryArcValues,queries.map steinerUnaryArcValues)
  let selected := queries.filter fun arc => decide (arc ∈ rows.toFinset)
  have exactSet : selected.toFinset = rows.toFinset := by
    ext arc
    simp only [selected,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun inside => ⟨List.mem_toFinset.mp (covers (List.mem_toFinset.mpr inside)),inside⟩⟩
  have simple : selected.Nodup := unique.filter _
  have count : steinerUnaryArcCount request = rows.toFinset.card := calc
    _ = selected.length := steinerUnaryArcCount_finite_queries rows queries
    _ = selected.toFinset.card := (List.toFinset_card_of_nodup simple).symm
    _ = _ := congrArg Finset.card exactSet
  simpa only [steinerUnaryArcCountAnswer,count] using steinerUnaryArcCountMachine_quadratic request

/-- Enumerate the candidate arcs in increasing source and target order. -/
def steinerAllArcQueries (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).product (List.finRange n)

theorem steinerAllArcQueries_nodup (n : ℕ) : (steinerAllArcQueries n).Nodup :=
  (List.nodup_finRange n).product (List.nodup_finRange n)

theorem steinerAllArcQueries_length (n : ℕ) : (steinerAllArcQueries n).length = n*n := by
  calc
    _ = (List.finRange n).length*(List.finRange n).length := List.length_product _ _
    _ = _ := by simp

theorem steinerAllArcQueries_cover {n : ℕ} (arc : Fin n × Fin n) : arc ∈ steinerAllArcQueries n := by
  exact List.mem_product.mpr ⟨List.mem_finRange _,List.mem_finRange _⟩

/-- The all-pairs query list satisfies coverage and uniqueness for every
finite arc graph, including empty graphs and rows repeated in the input. -/
def steinerUnaryArcCountMachine_all_pairs {n : ℕ} (rows : List (Fin n × Fin n)) :
    let queries := steinerAllArcQueries n
    let request : SteinerUnaryArcTable := (rows.map steinerUnaryArcValues,queries.map steinerUnaryArcValues)
    let X := (encodeSteinerUnaryArcTable request).length
    TM2OutputsInTime steinerUnaryArcCountMachine (encodeSteinerUnaryArcTable request)
      (some (List.replicate rows.toFinset.card (some true))) (5*X^2+16*X+6) := by
  exact steinerUnaryArcCountMachine_finset rows (steinerAllArcQueries n) (steinerAllArcQueries_nodup n)
    (fun arc _ => List.mem_toFinset.mpr (steinerAllArcQueries_cover arc))

end OnlineReachabilityPreservers
