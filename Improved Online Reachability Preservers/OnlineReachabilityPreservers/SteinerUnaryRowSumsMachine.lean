import OnlineReachabilityPreservers.SteinerForestScaleDistanceRounds
import OnlineReachabilityPreservers.SteinerUnaryProductMachine

/-! Sum each supplied row of unary operands using separate field and row delimiters. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private inductive UnaryRowSumLabel where
  | read
  | restore


private instance : Fintype UnaryRowSumLabel :=
  Fintype.ofEquiv Bool
    { toFun := fun b => if b then .restore else .read
      invFun := fun
        | .read => false
        | .restore => true
      left_inv b := by cases b <;> rfl
      right_inv label := by cases label <;> rfl }

private abbrev UnaryRowSumSymbol := Option Bool
private abbrev UnaryRowSumRegister := Option UnaryRowSumSymbol
private abbrev UnaryRowSumProgram :=
  Turing.TM2.Stmt (fun _ : Fin 2 => UnaryRowSumSymbol) UnaryRowSumLabel UnaryRowSumRegister

private def rowSumNext (label : UnaryRowSumLabel) : UnaryRowSumProgram :=
  load (fun _ => none) (goto (fun _ => label))

private def rowSumProgram : UnaryRowSumLabel → UnaryRowSumProgram
  | .read =>
    pop 0 (fun _ seen => seen) <|
      branch Option.isSome
        (branch (fun seen => seen.join.isSome)
          (push 1 (fun seen => seen.getD none) (rowSumNext .read))
          (rowSumNext .read))
        (rowSumNext .restore)
  | .restore =>
    pop 1 (fun _ seen => seen) <|
      branch Option.isSome
        (push 0 (fun seen => seen.getD none) (rowSumNext .restore))
        (load (fun _ => none) halt)

/-- Remove the separators between operands, keeping the row boundaries
and restoring the original order on the output stack. -/
abbrev steinerUnaryRowSumsMachine : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 0
  Γ _ := UnaryRowSumSymbol
  Λ := UnaryRowSumLabel
  main := .read
  σ := UnaryRowSumRegister
  initialState := none
  m := rowSumProgram

private def rowSumCfg (label : Option UnaryRowSumLabel) (input buffer : List UnaryRowSumSymbol) :
    steinerUnaryRowSumsMachine.Cfg where
  l := label
  var := none
  stk := ![input,buffer]

private theorem rowSum_update0 (input buffer word : List UnaryRowSumSymbol) :
    Function.update (![input,buffer] : Fin 2 → List UnaryRowSumSymbol) 0 word = ![word,buffer] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem rowSum_update1 (input buffer word : List UnaryRowSumSymbol) :
    Function.update (![input,buffer] : Fin 2 → List UnaryRowSumSymbol) 1 word = ![input,word] := by
  funext i
  fin_cases i <;> simp [Function.update]

private def rowSum_one {a b : steinerUnaryRowSumsMachine.Cfg}
    (move : steinerUnaryRowSumsMachine.step a = some b) :
    EvalsToInTime steinerUnaryRowSumsMachine.step a (some b) 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := move

private theorem rowSum_keep (value : Bool) (rest buffer : List UnaryRowSumSymbol) :
    steinerUnaryRowSumsMachine.step (rowSumCfg (some .read) (some value::rest) buffer) =
      some (rowSumCfg (some .read) rest (some value::buffer)) := by
  simp [FinTM2.step,steinerUnaryRowSumsMachine,rowSumCfg,rowSumProgram,rowSumNext,Turing.TM2.step,
    Turing.TM2.stepAux,rowSum_update0,rowSum_update1]
  rfl

private theorem rowSum_skip (rest buffer : List UnaryRowSumSymbol) :
    steinerUnaryRowSumsMachine.step (rowSumCfg (some .read) (none::rest) buffer) =
      some (rowSumCfg (some .read) rest buffer) := by
  simp [FinTM2.step,steinerUnaryRowSumsMachine,rowSumCfg,rowSumProgram,rowSumNext,Turing.TM2.step,
    Turing.TM2.stepAux,rowSum_update0]
  rfl

private theorem rowSum_readEnd (buffer : List UnaryRowSumSymbol) :
    steinerUnaryRowSumsMachine.step (rowSumCfg (some .read) [] buffer) =
      some (rowSumCfg (some .restore) [] buffer) := by
  simp [FinTM2.step,steinerUnaryRowSumsMachine,rowSumCfg,rowSumProgram,rowSumNext,Turing.TM2.step,
    Turing.TM2.stepAux,rowSum_update0]
  rfl

private def rowSum_read (input buffer : List UnaryRowSumSymbol) :
    EvalsToInTime steinerUnaryRowSumsMachine.step (rowSumCfg (some .read) input buffer)
      (some (rowSumCfg (some .restore) [] ((input.filter Option.isSome).reverse++buffer))) (input.length+1) := by
  induction input generalizing buffer with
  | nil => exact rowSum_one (rowSum_readEnd buffer)
  | cons symbol rest ih =>
    cases symbol with
    | none =>
      exact EvalsToInTime.trans _ _ _ _ _ _ (rowSum_one (rowSum_skip rest buffer)) (ih buffer)
    | some value =>
      have all := EvalsToInTime.trans _ _ _ _ _ _
        (rowSum_one (rowSum_keep value rest buffer)) (ih (some value::buffer))
      simpa only [List.filter_cons,Option.isSome_some,ite_true,List.reverse_cons,List.append_assoc,
        List.singleton_append,List.length_cons] using all

private theorem rowSum_put (value : UnaryRowSumSymbol) (output buffer : List UnaryRowSumSymbol) :
    steinerUnaryRowSumsMachine.step (rowSumCfg (some .restore) output (value::buffer)) =
      some (rowSumCfg (some .restore) (value::output) buffer) := by
  simp [FinTM2.step,steinerUnaryRowSumsMachine,rowSumCfg,rowSumProgram,rowSumNext,Turing.TM2.step,
    Turing.TM2.stepAux,rowSum_update0,rowSum_update1]
  rfl

private theorem rowSum_restoreEnd (output : List UnaryRowSumSymbol) :
    steinerUnaryRowSumsMachine.step (rowSumCfg (some .restore) output []) =
      some (rowSumCfg none output []) := by
  simp [FinTM2.step,steinerUnaryRowSumsMachine,rowSumCfg,rowSumProgram,Turing.TM2.step,
    Turing.TM2.stepAux,rowSum_update1]
  rfl

private def rowSum_restore (output buffer : List UnaryRowSumSymbol) :
    EvalsToInTime steinerUnaryRowSumsMachine.step (rowSumCfg (some .restore) output buffer)
      (some (rowSumCfg none (buffer.reverse++output) [])) (buffer.length+1) := by
  induction buffer generalizing output with
  | nil => exact rowSum_one (rowSum_restoreEnd output)
  | cons value buffer ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _
      (rowSum_one (rowSum_put value output buffer)) (ih (value::output))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons] using all

private theorem rowSum_init (word : List UnaryRowSumSymbol) :
    initList steinerUnaryRowSumsMachine word = rowSumCfg (some .read) word [] := by
  apply congrArg (fun stk : Fin 2 → List UnaryRowSumSymbol =>
    (⟨some .read,none,stk⟩ : steinerUnaryRowSumsMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem rowSum_halt (word : List UnaryRowSumSymbol) :
    haltList steinerUnaryRowSumsMachine word = rowSumCfg none word [] := by
  apply congrArg (fun stk : Fin 2 → List UnaryRowSumSymbol => (⟨none,none,stk⟩ : steinerUnaryRowSumsMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- The machine keeps both true tallies and row markers. It reads each
input symbol once and restores each kept symbol once. -/
def steinerUnaryRowSumsMachine_stream (word : List (Option Bool)) :
    let kept := word.filter Option.isSome
    TM2OutputsInTime steinerUnaryRowSumsMachine word (some kept) (word.length+kept.length+2) := by
  let kept := word.filter Option.isSome
  have read := rowSum_read word []
  rw [List.append_nil] at read
  have written := rowSum_restore [] kept.reverse
  rw [List.reverse_reverse,List.length_reverse,List.append_nil] at written
  have all := EvalsToInTime.trans _ _ _ _ _ _ read written
  change EvalsToInTime steinerUnaryRowSumsMachine.step (initList _ _) (some (haltList _ _)) _
  rw [rowSum_init,rowSum_halt]
  refine ⟨all.toEvalsTo,?_⟩
  have spent := all.steps_le_m
  change all.steps ≤ kept.length+1+(word.length+1) at spent
  change all.steps ≤ word.length+kept.length+2
  omega

private def rowSumFields (row : List ℕ) : List (Option Bool) :=
  row.flatMap fun value => List.replicate value (some true)++[none]

/-- Each unary operand ends with an inner delimiter. Each row, including
an empty row, ends with a separate row marker. -/
def encodeSteinerUnaryRowSums (rows : List (List ℕ)) : List (Option Bool) :=
  rows.flatMap fun row => rowSumFields row++[some false]

/-- Each unary sum has its own row delimiter. -/
def encodeSteinerUnaryRowSumTallies (totals : List ℕ) : List (Option Bool) :=
  totals.flatMap fun total => List.replicate total (some true)++[some false]

/-- One unary sum per row, in the order supplied. -/
def steinerUnaryRowSumsAnswer (rows : List (List ℕ)) : List (Option Bool) :=
  encodeSteinerUnaryRowSumTallies (rows.map List.sum)

private theorem rowSumFields_filter (row : List ℕ) :
    (rowSumFields row).filter Option.isSome = List.replicate row.sum (some true) := by
  induction row with
  | nil => rfl
  | cons value rest ih =>
    simp only [rowSumFields,List.flatMap_cons,List.filter_append,List.filter_replicate,
      Option.isSome_some,ite_true,List.filter_singleton,Option.isSome_none,
      List.sum_cons,List.replicate_add,List.append_assoc] at ih ⊢
    exact congrArg (List.replicate value (some true)++·) ih

theorem steinerUnaryRowSumsAnswer_eq (rows : List (List ℕ)) :
    (encodeSteinerUnaryRowSums rows).filter Option.isSome = steinerUnaryRowSumsAnswer rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [encodeSteinerUnaryRowSums,steinerUnaryRowSumsAnswer,encodeSteinerUnaryRowSumTallies,
      List.map_cons,List.flatMap_cons,List.filter_append,rowSumFields_filter,List.filter_singleton,
      Option.isSome_some,List.append_assoc] at ih ⊢
    rw [ih]
    rfl

/-- The row-sum machine reads and writes in linear time in the entire
encoded input, including both kinds of delimiter. -/
def steinerUnaryRowSumsMachine_run (rows : List (List ℕ)) :
    let input := encodeSteinerUnaryRowSums rows
    TM2OutputsInTime steinerUnaryRowSumsMachine input (some (steinerUnaryRowSumsAnswer rows)) (2*input.length+2) := by
  let input := encodeSteinerUnaryRowSums rows
  have run := steinerUnaryRowSumsMachine_stream input
  rw [steinerUnaryRowSumsAnswer_eq] at run
  refine ⟨run.toEvalsTo,?_⟩
  have length : (steinerUnaryRowSumsAnswer rows).length ≤ input.length := by
    rw [← steinerUnaryRowSumsAnswer_eq]
    exact List.length_filter_le Option.isSome input
  have spent := run.steps_le_m
  change run.steps ≤ 2*input.length+2
  omega

/-- The actual machine has a linear bound in its framed input length. -/
noncomputable def steinerUnaryRowSumsMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryRowSums id steinerUnaryRowSumsAnswer where
  tm := steinerUnaryRowSumsMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2*Polynomial.X+Polynomial.C 2
  outputsFun rows := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_X,
      Polynomial.eval_C] using steinerUnaryRowSumsMachine_run rows


open Finset

private def forestScaleRoundFields {n : ℕ} (dist : Fin n × Fin n → ℕ)
    (previous : Vector ℕ n) (root : Fin n) : List ℕ :=
  (List.ofFn fun (v : Fin n) =>
    let d := dist (v,root)
    if d ≤ n then [d,previous[v.val]] else []).flatten

/-- Supply the transfer weight and the previous rooted weight as
separate operands for each eligible pair, grouped by their new root. -/
def forestScaleRoundOperandRows {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) :
    List (List ℕ) :=
  List.ofFn (forestScaleRoundFields dist (inwardHeightWeightRounds dist h))

theorem forestScaleRoundOperandRows_sum {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) :
    (forestScaleRoundOperandRows dist h).map List.sum = (inwardHeightWeightRounds dist (h+1)).toList := by
  rw [forestScaleRoundOperandRows,List.map_ofFn,inwardHeightWeightRounds,Vector.toList_ofFn]
  apply congrArg (@List.ofFn ℕ n)
  funext root
  simp only [Function.comp_apply,forestScaleRoundFields,List.sum_flatten,List.map_ofFn,List.sum_ofFn]
  apply sum_congr rfl
  intro vertex _
  split_ifs <;> simp

private theorem rowSumFields_length (row : List ℕ) :
    (rowSumFields row).length = row.sum+row.length := by
  induction row with
  | nil => rfl
  | cons a row ih =>
    change (List.replicate a (some true)++[none]++rowSumFields row).length = _
    simp only [List.length_append,List.length_replicate,List.length_nil,List.sum_cons,List.length_cons,ih]
    omega

theorem encodeSteinerUnaryRowSums_length (rows : List (List ℕ)) :
    (encodeSteinerUnaryRowSums rows).length = (rows.map fun row => row.sum+row.length+1).sum := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    change (rowSumFields row++[some false]++encodeSteinerUnaryRowSums rows).length = _
    simp only [List.length_append,List.length_singleton,rowSumFields_length,ih,List.map_cons,List.sum_cons]

private theorem forestScaleRoundFields_bound {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) (root : Fin n) :
    let row := forestScaleRoundFields dist (inwardHeightWeightRounds dist h) root
    row.sum+row.length ≤ n*(n+inwardHeightWeightRoundBound n h+2) := by
  dsimp only [forestScaleRoundFields]
  rw [List.sum_flatten,List.length_flatten]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  rw [← sum_add_distrib]
  calc
    _ ≤ ∑ _ : Fin n, (n+inwardHeightWeightRoundBound n h+2) := by
      apply sum_le_sum
      intro v _
      split_ifs with eligible
      · have last := inwardHeightWeightRounds_get_le dist h v
        simp only [List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
        omega
      · simp
    _ = _ := by simp

/-- The prepared unary frame has polynomial magnitude at fixed height. -/
theorem encodeSteinerUnaryForestScaleRound_length_le {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) :
    (encodeSteinerUnaryRowSums (forestScaleRoundOperandRows dist h)).length ≤
      n*(n*(n+inwardHeightWeightRoundBound n h+2)+1) := by
  rw [encodeSteinerUnaryRowSums_length,forestScaleRoundOperandRows,List.map_ofFn,List.sum_ofFn]
  calc
    _ ≤ ∑ _ : Fin n, (n*(n+inwardHeightWeightRoundBound n h+2)+1) := by
      apply sum_le_sum
      intro root _
      exact Nat.succ_le_succ (forestScaleRoundFields_bound dist h root)
    _ = _ := by simp

/-- From the supplied ordered operand rows, the actual machine emits the
entire next-depth vector in its unary row encoding. -/
def steinerUnaryRowSumsMachine_forestRound {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) :
    let input := encodeSteinerUnaryRowSums (forestScaleRoundOperandRows dist h)
    TM2OutputsInTime steinerUnaryRowSumsMachine input
      (some (encodeSteinerUnaryRowSumTallies (inwardHeightWeightRounds dist (h+1)).toList)) (2*input.length+2) := by
  simpa only [steinerUnaryRowSumsAnswer,forestScaleRoundOperandRows_sum] using
    steinerUnaryRowSumsMachine_run (forestScaleRoundOperandRows dist h)

end OnlineReachabilityPreservers
