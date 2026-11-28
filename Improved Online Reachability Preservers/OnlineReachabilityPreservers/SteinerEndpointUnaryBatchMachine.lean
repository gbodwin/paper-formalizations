import OnlineReachabilityPreservers.SteinerBinaryToUnaryMachine
import OnlineReachabilityPreservers.SteinerStackFrame
import OnlineReachabilityPreservers.SteinerStackReturn

/-! Sequentially convert framed low-first endpoint words to unary indices. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev EndpointConvertLabel := steinerBinaryToUnaryMachine.Λ
private abbrev EndpointConvertRegister := steinerBinaryToUnaryMachine.σ
private instance : Fintype EndpointConvertLabel := steinerBinaryToUnaryMachine.ΛFin

private inductive EndpointBatchLabel where
  | readWord
  | convert (label : EndpointConvertLabel)
  | record
  | finish
  deriving Fintype

private abbrev EndpointBatchRegister := Option (Option Bool) × EndpointConvertRegister
private abbrev EndpointBatchProgram :=
  StackMachineTag.Program (Fin 6) (Option Bool) EndpointBatchLabel EndpointBatchRegister

private def endpointBatchInitial : EndpointBatchRegister :=
  (none,steinerBinaryToUnaryMachine.initialState)

private def endpointBatchObserve (_ : EndpointBatchRegister) (symbol : Option (Option Bool)) : EndpointBatchRegister :=
  (symbol,steinerBinaryToUnaryMachine.initialState)

private def endpointBatchTag :
    StackMachineTag Bool (Option Bool) EndpointConvertLabel EndpointBatchLabel EndpointConvertRegister EndpointBatchRegister where
  writeSymbol := some
  readSymbol := id
  writeRegister r := (none,r)
  readRegister r := r.2
  writeLabel := .convert
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def endpointBatchSlots : Fin 4 ↪ Fin 6 :=
  ⟨fun i => i.castSucc.castSucc,(Fin.castSucc_injective 5).comp (Fin.castSucc_injective 4)⟩

private def endpointBatchDigit : EndpointBatchLabel :=
  .convert ((steinerBinaryToUnaryPrepared []).l.getD steinerBinaryToUnaryMachine.main)

private def endpointBatchInner :
    EndpointBatchLabel → StackMachineTag.Program (Fin 4) (Option Bool) EndpointBatchLabel EndpointBatchRegister
  | .convert label => endpointBatchTag.returningStatement .record (steinerBinaryToUnaryMachine.m label)
  | _ => halt

private def endpointBatchNext (label : EndpointBatchLabel) : EndpointBatchProgram :=
  load (fun _ => endpointBatchInitial) (goto (fun _ => label))

private def endpointBatchProgram : EndpointBatchLabel → EndpointBatchProgram
  | .readWord =>
    pop 4 endpointBatchObserve <|
      branch (fun r => r.1.isSome)
        (branch (fun r => r.1.join.isSome)
          (push 1 (fun r => r.1.getD none) (endpointBatchNext .readWord))
          (endpointBatchNext endpointBatchDigit))
        (endpointBatchNext .finish)
  | .convert label => StackIndexEmbedding.statement endpointBatchSlots (endpointBatchInner (.convert label))
  | .record =>
    pop 2 endpointBatchObserve <|
      branch (fun r => r.1.isSome)
        (push 5 (fun r => r.1.getD none) (endpointBatchNext .record))
        (push 5 (fun _ => none) (endpointBatchNext .readWord))
  | .finish =>
    pop 5 endpointBatchObserve <|
      branch (fun r => r.1.isSome)
        (push 4 (fun r => r.1.getD none) (endpointBatchNext .finish))
        (load (fun _ => endpointBatchInitial) halt)

/-- Reverse one framed input at a time for the unary converter. Store the
framed answers in reverse order until the input batch is finished. -/
abbrev steinerEndpointUnaryBatchMachine : FinTM2 where
  K := Fin 6
  k₀ := 4
  k₁ := 4
  Γ _ := Option Bool
  Λ := EndpointBatchLabel
  main := .readWord
  σ := EndpointBatchRegister
  initialState := endpointBatchInitial
  m := endpointBatchProgram

private def endpointBatchCfg (label : Option EndpointBatchLabel) (bits tallies input answer : List (Option Bool)) :
    steinerEndpointUnaryBatchMachine.Cfg where
  l := label
  var := endpointBatchInitial
  stk := ![[],bits,tallies,[],input,answer]

private theorem endpointBatch_update1 (a b c d word : List (Option Bool)) :
    Function.update (![[],a,b,[],c,d] : Fin 6 → List (Option Bool)) 1 word = ![[],word,b,[],c,d] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem endpointBatch_update2 (a b c d word : List (Option Bool)) :
    Function.update (![[],a,b,[],c,d] : Fin 6 → List (Option Bool)) 2 word = ![[],a,word,[],c,d] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem endpointBatch_update4 (a b c d word : List (Option Bool)) :
    Function.update (![[],a,b,[],c,d] : Fin 6 → List (Option Bool)) 4 word = ![[],a,b,[],word,d] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem endpointBatch_update5 (a b c d word : List (Option Bool)) :
    Function.update (![[],a,b,[],c,d] : Fin 6 → List (Option Bool)) 5 word = ![[],a,b,[],c,word] := by
  funext i
  fin_cases i <;> simp [Function.update]

private def endpointBatch_one {a b : steinerEndpointUnaryBatchMachine.Cfg}
    (step : steinerEndpointUnaryBatchMachine.step a = some b) :
    EvalsToInTime steinerEndpointUnaryBatchMachine.step a (some b) 1 where
  steps := 1
  evals_in_steps := step
  steps_le_m := le_rfl

private theorem endpointBatch_readBit (bit : Bool) (word input out : List (Option Bool)) :
    steinerEndpointUnaryBatchMachine.step (endpointBatchCfg (some .readWord) word [] (some bit::input) out) =
      some (endpointBatchCfg (some .readWord) (some bit::word) [] input out) := by
  simp [FinTM2.step,steinerEndpointUnaryBatchMachine,endpointBatchCfg,Turing.TM2.step,Turing.TM2.stepAux,
    endpointBatchProgram,endpointBatchObserve,endpointBatchNext,endpointBatch_update1,endpointBatch_update4]
  rfl

private theorem endpointBatch_readDivider (word input out : List (Option Bool)) :
    steinerEndpointUnaryBatchMachine.step (endpointBatchCfg (some .readWord) word [] (none::input) out) =
      some (endpointBatchCfg (some endpointBatchDigit) word [] input out) := by
  simp [FinTM2.step,steinerEndpointUnaryBatchMachine,endpointBatchCfg,Turing.TM2.step,Turing.TM2.stepAux,
    endpointBatchProgram,endpointBatchObserve,endpointBatchNext,endpointBatch_update4]
  rfl

private theorem endpointBatch_readEnd (out : List (Option Bool)) :
    steinerEndpointUnaryBatchMachine.step (endpointBatchCfg (some .readWord) [] [] [] out) =
      some (endpointBatchCfg (some .finish) [] [] [] out) := by
  simp [FinTM2.step,steinerEndpointUnaryBatchMachine,endpointBatchCfg,Turing.TM2.step,Turing.TM2.stepAux,
    endpointBatchProgram,endpointBatchObserve,endpointBatchNext,endpointBatch_update4]
  rfl

private def endpointBatch_read (word : List Bool) (moved input out : List (Option Bool)) :
    EvalsToInTime steinerEndpointUnaryBatchMachine.step
      (endpointBatchCfg (some .readWord) moved [] (word.map some++none::input) out)
      (some (endpointBatchCfg (some endpointBatchDigit) ((word.map some).reverse++moved) [] input out))
      (word.length+1) := by
  induction word generalizing moved with
  | nil => exact endpointBatch_one (endpointBatch_readDivider moved input out)
  | cons bit word ih =>
    have action := endpointBatch_one (endpointBatch_readBit bit moved (word.map some++none::input) out)
    have all := EvalsToInTime.trans _ _ _ _ _ _ action (ih (some bit::moved))
    simpa only [List.map_cons,List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,
      List.length_cons,List.nil_append] using all

private theorem endpointBatch_recordSymbol (symbol : Option Bool) (tallies input out : List (Option Bool)) :
    steinerEndpointUnaryBatchMachine.step (endpointBatchCfg (some .record) [] (symbol::tallies) input out) =
      some (endpointBatchCfg (some .record) [] tallies input (symbol::out)) := by
  simp [FinTM2.step,steinerEndpointUnaryBatchMachine,endpointBatchCfg,Turing.TM2.step,Turing.TM2.stepAux,
    endpointBatchProgram,endpointBatchObserve,endpointBatchNext,endpointBatch_update2,endpointBatch_update5]
  rfl

private theorem endpointBatch_recordEnd (input out : List (Option Bool)) :
    steinerEndpointUnaryBatchMachine.step (endpointBatchCfg (some .record) [] [] input out) =
      some (endpointBatchCfg (some .readWord) [] [] input (none::out)) := by
  simp [FinTM2.step,steinerEndpointUnaryBatchMachine,endpointBatchCfg,Turing.TM2.step,Turing.TM2.stepAux,
    endpointBatchProgram,endpointBatchObserve,endpointBatchNext,endpointBatch_update2,endpointBatch_update5]
  rfl

private def endpointBatch_record (tallies input out : List (Option Bool)) :
    EvalsToInTime steinerEndpointUnaryBatchMachine.step (endpointBatchCfg (some .record) [] tallies input out)
      (some (endpointBatchCfg (some .readWord) [] [] input (none::(tallies.reverse++out)))) (tallies.length+1) := by
  induction tallies generalizing out with
  | nil => exact endpointBatch_one (endpointBatch_recordEnd input out)
  | cons symbol tallies ih =>
    have action := endpointBatch_one (endpointBatch_recordSymbol symbol tallies input out)
    have all := EvalsToInTime.trans _ _ _ _ _ _ action (ih (symbol::out))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons] using all

private theorem endpointBatch_finishSymbol (symbol : Option Bool) (buffer out : List (Option Bool)) :
    steinerEndpointUnaryBatchMachine.step (endpointBatchCfg (some .finish) [] [] out (symbol::buffer)) =
      some (endpointBatchCfg (some .finish) [] [] (symbol::out) buffer) := by
  simp [FinTM2.step,steinerEndpointUnaryBatchMachine,endpointBatchCfg,Turing.TM2.step,Turing.TM2.stepAux,
    endpointBatchProgram,endpointBatchObserve,endpointBatchNext,endpointBatch_update4,endpointBatch_update5]
  rfl

private theorem endpointBatch_finishEnd (out : List (Option Bool)) :
    steinerEndpointUnaryBatchMachine.step (endpointBatchCfg (some .finish) [] [] out []) =
      some (endpointBatchCfg none [] [] out []) := by
  simp [FinTM2.step,steinerEndpointUnaryBatchMachine,endpointBatchCfg,Turing.TM2.step,Turing.TM2.stepAux,
    endpointBatchProgram,endpointBatchObserve,endpointBatch_update5]
  rfl

private def endpointBatch_finish (buffer out : List (Option Bool)) :
    EvalsToInTime steinerEndpointUnaryBatchMachine.step (endpointBatchCfg (some .finish) [] [] out buffer)
      (some (endpointBatchCfg none [] [] (buffer.reverse++out) [])) (buffer.length+1) := by
  induction buffer generalizing out with
  | nil => exact endpointBatch_one (endpointBatch_finishEnd out)
  | cons symbol buffer ih =>
    have action := endpointBatch_one (endpointBatch_finishSymbol symbol buffer out)
    have all := EvalsToInTime.trans _ _ _ _ _ _ action (ih (symbol::out))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons] using all

private def endpointBatchPassive (input out : List (Option Bool)) (i : Fin 6) : List (Option Bool) :=
  if i = 4 then input else if i = 5 then out else []

private theorem endpointBatchSlots_excludes_input (i : Fin 4) : endpointBatchSlots i ≠ 4 := by
  fin_cases i <;> decide

private theorem endpointBatchSlots_excludes_output (i : Fin 4) : endpointBatchSlots i ≠ 5 := by
  fin_cases i <;> decide

private noncomputable def endpointBatchTranslated (input out : List (Option Bool)) (c : steinerBinaryToUnaryMachine.Cfg) :
    steinerEndpointUnaryBatchMachine.Cfg :=
  StackIndexEmbedding.configuration endpointBatchSlots (endpointBatchPassive input out)
    (endpointBatchTag.returningConfiguration .record c)

private theorem endpointBatch_convertStep (input out : List (Option Bool))
    {c after : steinerBinaryToUnaryMachine.Cfg} (move : steinerBinaryToUnaryMachine.step c = some after) :
    steinerEndpointUnaryBatchMachine.step (endpointBatchTranslated input out c) =
      some (endpointBatchTranslated input out after) := by
  have tagged := endpointBatchTag.step_embedded_return .record (base := steinerBinaryToUnaryMachine.m)
    (host := endpointBatchInner) (fun _ => rfl) move
  have framed := StackIndexEmbedding.step_on endpointBatchSlots (base := endpointBatchInner)
    (endpointBatchPassive input out) (endpointBatchTag.returningConfiguration .record c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem endpointBatch_convertTapes (input out : List (Option Bool)) (c : steinerBinaryToUnaryMachine.Cfg)
    (bits tallies : List Bool) (tapes : c.stk = ![[],bits,tallies,[]]) :
    (endpointBatchTranslated input out c).stk = ![[],bits.map some,tallies.map some,[],input,out] := by
  have image (i : Fin 4) : (endpointBatchTranslated input out c).stk (endpointBatchSlots i) =
      ((![[],bits,tallies,[]] : Fin 4 → List Bool) i).map some := by
    change StackIndexEmbedding.tapesAt endpointBatchSlots (fun i => (c.stk i).map some) _ (endpointBatchSlots i) = _
    rw [StackIndexEmbedding.tapesAt_image,tapes]
  funext i
  fin_cases i
  · exact image 0
  · exact image 1
  · exact image 2
  · exact image 3
  · change StackIndexEmbedding.tapesAt endpointBatchSlots _ (endpointBatchPassive input out) 4 = _
    rw [StackIndexEmbedding.tapesAt_extra _ _ _ endpointBatchSlots_excludes_input,endpointBatchPassive,ite_eq_left rfl]
    rfl
  · change StackIndexEmbedding.tapesAt endpointBatchSlots _ (endpointBatchPassive input out) 5 = _
    rw [StackIndexEmbedding.tapesAt_extra _ _ _ endpointBatchSlots_excludes_output,endpointBatchPassive,
      ite_eq_right (by decide : (5 : Fin 6) ≠ 4),ite_eq_left rfl]
    rfl

private theorem endpointBatch_convertInit (word : List Bool) (input out : List (Option Bool)) :
    endpointBatchTranslated input out (steinerBinaryToUnaryPrepared word) =
      endpointBatchCfg (some endpointBatchDigit) ((word.map some).reverse) [] input out := by
  apply congrArg (fun stk : Fin 6 → List (Option Bool) =>
    (⟨some endpointBatchDigit,endpointBatchInitial,stk⟩ : steinerEndpointUnaryBatchMachine.Cfg))
  rw [← List.map_reverse]
  exact endpointBatch_convertTapes input out (steinerBinaryToUnaryPrepared word) word.reverse [] rfl

private theorem endpointBatch_convertReturn (tallies : List Bool) (input out : List (Option Bool)) :
    endpointBatchTranslated input out (haltList steinerBinaryToUnaryMachine tallies) =
      endpointBatchCfg (some .record) [] (tallies.map some) input out := by
  apply congrArg (fun stk : Fin 6 → List (Option Bool) =>
    (⟨some .record,endpointBatchInitial,stk⟩ : steinerEndpointUnaryBatchMachine.Cfg))
  exact endpointBatch_convertTapes input out (haltList steinerBinaryToUnaryMachine tallies) [] tallies (by
    funext i
    fin_cases i <;> rfl)

private def endpointBatch_convert (word : List Bool) (input out : List (Option Bool)) :
    EvalsToInTime steinerEndpointUnaryBatchMachine.step
      (endpointBatchCfg (some endpointBatchDigit) ((word.map some).reverse) [] input out)
      (some (endpointBatchCfg (some .record) [] ((encodeSteinerUnaryProductCount (binaryWordValue word)).map some) input out))
      (3*word.length+3*binaryWordValue word+1) := by
  let run := steinerBinaryToUnaryMachine_finishPrepared word
  refine ⟨⟨run.steps,?_⟩,run.steps_le_m⟩
  have executed := iterate_map_some (endpointBatchTranslated input out) (fun move => endpointBatch_convertStep input out move)
    run.steps run.evals_in_steps
  change (flip bind steinerEndpointUnaryBatchMachine.step)^[run.steps]
      (some (endpointBatchTranslated input out (steinerBinaryToUnaryPrepared word))) =
    some (endpointBatchTranslated input out
      (haltList steinerBinaryToUnaryMachine (encodeSteinerUnaryProductCount (binaryWordValue word)))) at executed
  rw [endpointBatch_convertInit,endpointBatch_convertReturn] at executed
  exact executed

private def endpointWordFrame (word : List Bool) : List (Option Bool) :=
  word.map some ++ [none]

/-- An explicit delimiter follows every input word, including the empty word. -/
def encodeSteinerBinaryEndpointWords (words : List (List Bool)) : List (Option Bool) :=
  words.flatMap endpointWordFrame

/-- The output lists one unary word for each input endpoint, in order. -/
def encodeSteinerUnaryEndpointValues (values : List ℕ) : List (Option Bool) :=
  values.flatMap (endpointWordFrame ∘ encodeSteinerUnaryProductCount)

theorem encodeSteinerBinaryEndpointWords_length (words : List (List Bool)) :
    (encodeSteinerBinaryEndpointWords words).length = (words.map List.length).sum+words.length := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    simp only [encodeSteinerBinaryEndpointWords,List.flatMap_cons,List.length_append,endpointWordFrame,
      List.length_map,List.length_cons,List.length_nil,List.map_cons,List.sum_cons] at ih ⊢
    omega

theorem encodeSteinerUnaryEndpointValues_length (values : List ℕ) :
    (encodeSteinerUnaryEndpointValues values).length = values.sum+values.length := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [encodeSteinerUnaryEndpointValues,List.flatMap_cons,List.length_append,Function.comp_apply,
      endpointWordFrame,encodeSteinerUnaryProductCount,List.length_map,List.length_replicate,List.length_cons,
      List.length_nil,List.sum_cons] at ih ⊢
    omega

private def endpointBatch_all (words : List (List Bool)) (out : List (Option Bool)) :
    EvalsToInTime steinerEndpointUnaryBatchMachine.step
      (endpointBatchCfg (some .readWord) [] [] (encodeSteinerBinaryEndpointWords words) out)
      (some (endpointBatchCfg (some .finish) [] [] []
        ((encodeSteinerUnaryEndpointValues (words.map binaryWordValue)).reverse++out)))
      (3*(encodeSteinerBinaryEndpointWords words).length+(words.map List.length).sum+
        4*(words.map binaryWordValue).sum+1) := by
  induction words generalizing out with
  | nil => exact endpointBatch_one (endpointBatch_readEnd out)
  | cons word words ih =>
    let input := encodeSteinerBinaryEndpointWords words
    let tallies := (encodeSteinerUnaryProductCount (binaryWordValue word)).map some
    let new := none::(tallies.reverse++out)
    have read := endpointBatch_read word [] input out
    rw [List.append_nil] at read
    have converted := EvalsToInTime.trans _ _ _ _ _ _ read (endpointBatch_convert word input out)
    have length : tallies.length = binaryWordValue word := by simp [tallies,encodeSteinerUnaryProductCount]
    have record := endpointBatch_record tallies input out
    rw [length] at record
    have ready := EvalsToInTime.trans _ _ _ _ _ _ converted record
    have all := EvalsToInTime.trans _ _ _ _ _ _ ready (ih new)
    have inputWord : encodeSteinerBinaryEndpointWords (word::words) = word.map some++none::input := by
      simp [encodeSteinerBinaryEndpointWords,endpointWordFrame,input,List.append_assoc]
    have outputWord : encodeSteinerUnaryEndpointValues ((word::words).map binaryWordValue) =
        (tallies++[none])++encodeSteinerUnaryEndpointValues (words.map binaryWordValue) := by
      simp [encodeSteinerUnaryEndpointValues,endpointWordFrame,tallies]
    have pay : all.steps ≤
        3*(encodeSteinerBinaryEndpointWords (word::words)).length+((word::words).map List.length).sum+
          4*((word::words).map binaryWordValue).sum+1 := by
      have spent := all.steps_le_m
      rw [inputWord]
      simp only [List.length_append,List.length_map,List.length_cons,List.map_cons,List.sum_cons]
      dsimp only [input] at *
      omega
    rw [inputWord,outputWord,List.reverse_append,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
      List.singleton_append,List.append_assoc]
    exact ⟨all.toEvalsTo,by simpa only [inputWord] using pay⟩

private theorem endpointBatch_init (input : List (Option Bool)) :
    initList steinerEndpointUnaryBatchMachine input = endpointBatchCfg (some .readWord) [] [] input [] := by
  apply congrArg (fun stk : Fin 6 → List (Option Bool) =>
    (⟨some .readWord,endpointBatchInitial,stk⟩ : steinerEndpointUnaryBatchMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem endpointBatch_halt (out : List (Option Bool)) :
    haltList steinerEndpointUnaryBatchMachine out = endpointBatchCfg none [] [] out [] := by
  apply congrArg (fun stk : Fin 6 → List (Option Bool) =>
    (⟨none,endpointBatchInitial,stk⟩ : steinerEndpointUnaryBatchMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- Convert the framed words in order, with a bound in their complete
framed input length and the sum of their numerical values. -/
def steinerEndpointUnaryBatchMachine_run (words : List (List Bool)) :
    TM2OutputsInTime steinerEndpointUnaryBatchMachine (encodeSteinerBinaryEndpointWords words)
      (some (encodeSteinerUnaryEndpointValues (words.map binaryWordValue)))
      (4*(encodeSteinerBinaryEndpointWords words).length+5*(words.map binaryWordValue).sum+2) := by
  let out := encodeSteinerUnaryEndpointValues (words.map binaryWordValue)
  have converted := endpointBatch_all words []
  rw [List.append_nil] at converted
  have finish := endpointBatch_finish out.reverse []
  rw [List.reverse_reverse,List.append_nil,List.length_reverse] at finish
  have all := EvalsToInTime.trans _ _ _ _ _ _ converted finish
  change EvalsToInTime steinerEndpointUnaryBatchMachine.step _ (some (haltList steinerEndpointUnaryBatchMachine _)) _
  rw [endpointBatch_init,endpointBatch_halt]
  refine ⟨all.toEvalsTo,all.steps_le_m.trans ?_⟩
  dsimp only [out]
  rw [encodeSteinerUnaryEndpointValues_length,List.length_map,encodeSteinerBinaryEndpointWords_length]
  omega

private theorem endpointBatch_sum_le_count_mul {n : ℕ} (words : List (List Bool))
    (valid : ∀ word ∈ words, binaryWordValue word < n) :
    (words.map binaryWordValue).sum ≤ words.length*n := by
  induction words with
  | nil => simp
  | cons word words ih =>
    have first := (valid word (List.mem_cons_self)).le
    have later := ih (fun w member => valid w (List.mem_cons_of_mem _ member))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    omega

/-- All accepted values can be converted in time linear in the input
length plus the vertex count times the number of endpoints. -/
def steinerEndpointUnaryBatchMachine_valid {n : ℕ} (words : List (List Bool))
    (valid : ∀ word ∈ words, binaryWordValue word < n) :
    TM2OutputsInTime steinerEndpointUnaryBatchMachine (encodeSteinerBinaryEndpointWords words)
      (some (encodeSteinerUnaryEndpointValues (words.map binaryWordValue)))
      (4*(encodeSteinerBinaryEndpointWords words).length+5*(words.length*n)+2) := by
  have run := steinerEndpointUnaryBatchMachine_run words
  have paid := endpointBatch_sum_le_count_mul words valid
  exact ⟨run.toEvalsTo,run.steps_le_m.trans (by omega)⟩

/-- Flatten each graph row into its two successive endpoint frames. -/
def steinerRawGraphEndpointWords (rows : List SteinerRangeWordPair) : List (List Bool) :=
  rows.flatMap fun pair => [pair.1,pair.2]

private theorem rawGraphEndpointWords_length (rows : List SteinerRangeWordPair) :
    (steinerRawGraphEndpointWords rows).length = 2*rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [steinerRawGraphEndpointWords,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at ih ⊢
    omega

private theorem rawGraphEndpointWords_bits (rows : List SteinerRangeWordPair) :
    ((steinerRawGraphEndpointWords rows).map List.length).sum = binaryEndpointBits rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [steinerRawGraphEndpointWords,List.flatMap_cons,List.map_append,List.map_cons,List.map_nil,List.sum_append,
      List.sum_cons,List.sum_nil,binaryEndpointBits] at ih ⊢
    omega

private theorem rawGraphEndpointWords_values (rows : List SteinerRangeWordPair) :
    (steinerRawGraphEndpointWords rows).map binaryWordValue =
      (rows.map (fun row => (binaryWordValue row.1,binaryWordValue row.2))).flatMap (fun pair => [pair.1,pair.2]) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simpa only [steinerRawGraphEndpointWords,List.flatMap_cons,List.map_append,List.map_cons,List.map_nil,
      List.cons_append,List.nil_append] using congrArg (fun tail => binaryWordValue row.1::binaryWordValue row.2::tail) ih

/-- On graph input accepted by the guarded decoder, the emitted unary
indices are exactly the decoded finite endpoint values in row order. -/
def steinerEndpointUnaryBatchMachine_guardedGraph {n : ℕ} (allowance : ℕ)
    (rows : List SteinerRangeWordPair) (decoded : List (Fin n × Fin n))
    (accepted : (decodeCheckedBinaryFinArcRowsWithWork allowance rows).1 = some decoded) :
    TM2OutputsInTime steinerEndpointUnaryBatchMachine
      (encodeSteinerBinaryEndpointWords (steinerRawGraphEndpointWords rows))
      (some (encodeSteinerUnaryEndpointValues (decoded.flatMap fun pair => [pair.1.val,pair.2.val])))
      (4*binaryEndpointBits rows+8*rows.length+10*(rows.length*n)+2) := by
  have legal := (decodeCheckedBinaryFinArcRowsWithWork_some_iff_valid allowance rows).mp ⟨decoded,accepted⟩
  have endpoints : ∀ word ∈ steinerRawGraphEndpointWords rows, binaryWordValue word < n := by
    intro word present
    obtain ⟨row,rowIn,endpoint⟩ := List.mem_flatMap.mp present
    obtain ⟨_,first,second⟩ := legal row rowIn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at endpoint
    rcases endpoint with rfl | rfl
    · exact first
    · exact second
  have same := ((decodeCheckedBinaryFinArcRowsWithWork_eq_some_iff allowance rows decoded).mp accepted).2
  have exactValues : (steinerRawGraphEndpointWords rows).map binaryWordValue =
      decoded.flatMap (fun pair => [pair.1.val,pair.2.val]) := by
    rw [rawGraphEndpointWords_values,← same,List.flatMap_map]
  have run := steinerEndpointUnaryBatchMachine_valid (steinerRawGraphEndpointWords rows) endpoints
  rw [exactValues] at run
  refine ⟨run.toEvalsTo,run.steps_le_m.trans ?_⟩
  rw [encodeSteinerBinaryEndpointWords_length,rawGraphEndpointWords_bits,rawGraphEndpointWords_length]
  ring_nf
  exact le_rfl

end OnlineReachabilityPreservers
