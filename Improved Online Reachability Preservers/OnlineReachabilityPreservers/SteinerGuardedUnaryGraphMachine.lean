import OnlineReachabilityPreservers.SteinerEndpointUnaryBatchMachine
import OnlineReachabilityPreservers.SteinerSingleBoundStartupMachine

/-! Validate a graph supplied with one bound, then convert its exact endpoint words. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev GraphGuardLabel := steinerSingleBoundStartupMachine.Λ
private abbrev GraphGuardRegister := steinerSingleBoundStartupMachine.σ
private abbrev GraphDecodeLabel := steinerEndpointUnaryBatchMachine.Λ
private abbrev GraphDecodeRegister := steinerEndpointUnaryBatchMachine.σ
private instance : Fintype GraphGuardLabel := steinerSingleBoundStartupMachine.ΛFin
private instance : Fintype GraphDecodeLabel := steinerEndpointUnaryBatchMachine.ΛFin

private inductive GuardedUnaryGraphLabel where
  | save
  | restore
  | guard (label : GraphGuardLabel)
  | branchOnFlag
  | restoreWords
  | skipBound
  | discardWords
  | decode (label : GraphDecodeLabel)
  deriving Fintype

private abbrev GraphSymbol := SteinerRawRangeSeedSymbol
private abbrev GuardedUnaryGraphRegister := Option GraphSymbol × GraphGuardRegister × GraphDecodeRegister
private abbrev GuardedUnaryGraphProgram :=
  StackMachineTag.Program (Fin 7) GraphSymbol GuardedUnaryGraphLabel GuardedUnaryGraphRegister

private def guardedUnaryGraphInitial : GuardedUnaryGraphRegister :=
  (none,steinerSingleBoundStartupMachine.initialState,steinerEndpointUnaryBatchMachine.initialState)

private def guardedUnaryGraphObserve (_ : GuardedUnaryGraphRegister) (seen : Option GraphSymbol) : GuardedUnaryGraphRegister :=
  (seen,steinerSingleBoundStartupMachine.initialState,steinerEndpointUnaryBatchMachine.initialState)

private def guardedUnaryGraphNext (label : GuardedUnaryGraphLabel) : GuardedUnaryGraphProgram :=
  load (fun _ => guardedUnaryGraphInitial) (goto (fun _ => label))

private def guardedUnaryGraphCheckTag :
    StackMachineTag GraphSymbol GraphSymbol GraphGuardLabel GuardedUnaryGraphLabel
      GraphGuardRegister GuardedUnaryGraphRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (none,r,steinerEndpointUnaryBatchMachine.initialState)
  readRegister r := r.2.1
  writeLabel := .guard
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def guardedUnaryGraphDecodeTag :
    StackMachineTag (Option Bool) GraphSymbol GraphDecodeLabel GuardedUnaryGraphLabel
      GraphDecodeRegister GuardedUnaryGraphRegister where
  writeSymbol := Sum.inr
  readSymbol
    | .inl _ => none
    | .inr bit => some bit
  writeRegister r := (none,steinerSingleBoundStartupMachine.initialState,r)
  readRegister r := r.2.2
  writeLabel := .decode
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def guardedUnaryGraphCheckSlots : Fin 5 ↪ Fin 7 :=
  ⟨fun i => i.castSucc.castSucc,(Fin.castSucc_injective 6).comp (Fin.castSucc_injective 5)⟩

private def guardedUnaryGraphDecodeSlots : Fin 6 ↪ Fin 7 :=
  ⟨Fin.castSucc,Fin.castSucc_injective _⟩

private def guardedUnaryGraphGuardInner :
    GuardedUnaryGraphLabel → StackMachineTag.Program (Fin 5) GraphSymbol GuardedUnaryGraphLabel GuardedUnaryGraphRegister
  | .guard label =>
    guardedUnaryGraphCheckTag.returningStatement .branchOnFlag (steinerSingleBoundStartupMachine.m label)
  | _ => halt

private def guardedUnaryGraphDecodeFramed (label : GraphDecodeLabel) :
    StackMachineTag.Program (Fin 7) (Option Bool) GraphDecodeLabel GraphDecodeRegister :=
  StackIndexEmbedding.statement guardedUnaryGraphDecodeSlots (steinerEndpointUnaryBatchMachine.m label)

private def guardedUnaryGraphPassed : Option GraphSymbol → Bool
  | some (.inr _) => true
  | _ => false

private def guardedUnaryGraphRawBit : GraphSymbol → Option Bool
  | .inl (some symbol) => symbol
  | _ => none

private def guardedUnaryGraphIsWordBit : Option GraphSymbol → Bool
  | some (.inr (some _)) => true
  | _ => false

private def guardedUnaryGraphProgram : GuardedUnaryGraphLabel → GuardedUnaryGraphProgram
  | .save =>
    pop 4 guardedUnaryGraphObserve <|
      branch (fun r => r.1.isSome)
        (push 0 (fun r => r.1.getD (Sum.inl none)) <|
          push 6 (fun r => r.1.getD (Sum.inl none)) (guardedUnaryGraphNext .save))
        (guardedUnaryGraphNext .restore)
  | .restore =>
    pop 0 guardedUnaryGraphObserve <|
      branch (fun r => r.1.isSome)
        (push 4 (fun r => r.1.getD (Sum.inl none)) (guardedUnaryGraphNext .restore))
        (guardedUnaryGraphNext (.guard steinerSingleBoundStartupMachine.main))
  | .guard label => StackIndexEmbedding.statement guardedUnaryGraphCheckSlots (guardedUnaryGraphGuardInner (.guard label))
  | .branchOnFlag =>
    pop 4 guardedUnaryGraphObserve <|
      branch (fun r => guardedUnaryGraphPassed r.1)
        (guardedUnaryGraphNext .restoreWords) (guardedUnaryGraphNext .discardWords)
  | .restoreWords =>
    pop 6 guardedUnaryGraphObserve <|
      branch (fun r => r.1.isSome)
        (push 4 (fun r => Sum.inr (guardedUnaryGraphRawBit (r.1.getD (Sum.inl none))))
          (guardedUnaryGraphNext .restoreWords))
        (guardedUnaryGraphNext .skipBound)
  | .skipBound =>
    pop 4 guardedUnaryGraphObserve <|
      branch (fun r => guardedUnaryGraphIsWordBit r.1)
        (guardedUnaryGraphNext .skipBound)
        (guardedUnaryGraphNext (.decode steinerEndpointUnaryBatchMachine.main))
  | .discardWords =>
    pop 6 guardedUnaryGraphObserve <|
      branch (fun r => r.1.isSome) (guardedUnaryGraphNext .discardWords)
        (push 4 (fun _ => Sum.inl none) (load (fun _ => guardedUnaryGraphInitial) halt))
  | .decode label => guardedUnaryGraphDecodeTag.statement (guardedUnaryGraphDecodeFramed label)

/-- Read a graph with one bound word. Keep a copy of the endpoint word
frames while checking the graph. On acceptance convert the original
endpoints to unary. Graph rejection returns a single left-tagged marker. -/
abbrev steinerGuardedUnaryGraphMachine : FinTM2 where
  K := Fin 7
  k₀ := 4
  k₁ := 4
  Γ _ := GraphSymbol
  Λ := GuardedUnaryGraphLabel
  main := .save
  σ := GuardedUnaryGraphRegister
  initialState := guardedUnaryGraphInitial
  m := guardedUnaryGraphProgram

private def guardedUnaryGraphCfg (label : Option GuardedUnaryGraphLabel)
    (buffer input stored : List GraphSymbol) : steinerGuardedUnaryGraphMachine.Cfg where
  l := label
  var := guardedUnaryGraphInitial
  stk := ![buffer,[],[],[],input,[],stored]

private theorem guardedUnaryGraph_update0 (buffer input stored word : List GraphSymbol) :
    Function.update (![buffer,[],[],[],input,[],stored] : Fin 7 → List GraphSymbol) 0 word =
      ![word,[],[],[],input,[],stored] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem guardedUnaryGraph_update4 (buffer input stored word : List GraphSymbol) :
    Function.update (![buffer,[],[],[],input,[],stored] : Fin 7 → List GraphSymbol) 4 word =
      ![buffer,[],[],[],word,[],stored] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem guardedUnaryGraph_update6 (buffer input stored word : List GraphSymbol) :
    Function.update (![buffer,[],[],[],input,[],stored] : Fin 7 → List GraphSymbol) 6 word =
      ![buffer,[],[],[],input,[],word] := by
  funext i
  fin_cases i <;> simp [Function.update]

private def guardedUnaryGraph_one {a b : steinerGuardedUnaryGraphMachine.Cfg}
    (step : steinerGuardedUnaryGraphMachine.step a = some b) :
    EvalsToInTime steinerGuardedUnaryGraphMachine.step a (some b) 1 where
  steps := 1
  evals_in_steps := step
  steps_le_m := le_rfl

private theorem guardedUnaryGraph_saveSymbol (symbol : GraphSymbol) (buffer input stored : List GraphSymbol) :
    steinerGuardedUnaryGraphMachine.step (guardedUnaryGraphCfg (some .save) buffer (symbol::input) stored) =
      some (guardedUnaryGraphCfg (some .save) (symbol::buffer) input (symbol::stored)) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphMachine,guardedUnaryGraphCfg,Turing.TM2.step,Turing.TM2.stepAux,
    guardedUnaryGraphProgram,guardedUnaryGraphObserve,guardedUnaryGraphNext,
    guardedUnaryGraph_update0,guardedUnaryGraph_update4,guardedUnaryGraph_update6]
  rfl

private theorem guardedUnaryGraph_saveEnd (buffer stored : List GraphSymbol) :
    steinerGuardedUnaryGraphMachine.step (guardedUnaryGraphCfg (some .save) buffer [] stored) =
      some (guardedUnaryGraphCfg (some .restore) buffer [] stored) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphMachine,guardedUnaryGraphCfg,Turing.TM2.step,Turing.TM2.stepAux,
    guardedUnaryGraphProgram,guardedUnaryGraphObserve,guardedUnaryGraphNext,guardedUnaryGraph_update4]
  rfl

private def guardedUnaryGraph_save (input buffer stored : List GraphSymbol) :
    EvalsToInTime steinerGuardedUnaryGraphMachine.step (guardedUnaryGraphCfg (some .save) buffer input stored)
      (some (guardedUnaryGraphCfg (some .restore) (input.reverse++buffer) [] (input.reverse++stored))) (input.length+1) := by
  induction input generalizing buffer stored with
  | nil => exact guardedUnaryGraph_one (guardedUnaryGraph_saveEnd buffer stored)
  | cons symbol input ih =>
    have first := guardedUnaryGraph_one (guardedUnaryGraph_saveSymbol symbol buffer input stored)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (symbol::buffer) (symbol::stored))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons] using all

private theorem guardedUnaryGraph_restoreSymbol (symbol : GraphSymbol) (buffer input stored : List GraphSymbol) :
    steinerGuardedUnaryGraphMachine.step (guardedUnaryGraphCfg (some .restore) (symbol::buffer) input stored) =
      some (guardedUnaryGraphCfg (some .restore) buffer (symbol::input) stored) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphMachine,guardedUnaryGraphCfg,Turing.TM2.step,Turing.TM2.stepAux,
    guardedUnaryGraphProgram,guardedUnaryGraphObserve,guardedUnaryGraphNext,guardedUnaryGraph_update0,guardedUnaryGraph_update4]
  rfl

private theorem guardedUnaryGraph_restoreEnd (input stored : List GraphSymbol) :
    steinerGuardedUnaryGraphMachine.step (guardedUnaryGraphCfg (some .restore) [] input stored) =
      some (guardedUnaryGraphCfg (some (.guard steinerSingleBoundStartupMachine.main)) [] input stored) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphMachine,guardedUnaryGraphCfg,Turing.TM2.step,Turing.TM2.stepAux,
    guardedUnaryGraphProgram,guardedUnaryGraphObserve,guardedUnaryGraphNext,guardedUnaryGraph_update0]
  rfl

private def guardedUnaryGraph_restore (buffer input stored : List GraphSymbol) :
    EvalsToInTime steinerGuardedUnaryGraphMachine.step (guardedUnaryGraphCfg (some .restore) buffer input stored)
      (some (guardedUnaryGraphCfg (some (.guard steinerSingleBoundStartupMachine.main)) [] (buffer.reverse++input) stored))
      (buffer.length+1) := by
  induction buffer generalizing input with
  | nil => exact guardedUnaryGraph_one (guardedUnaryGraph_restoreEnd input stored)
  | cons symbol buffer ih =>
    have first := guardedUnaryGraph_one (guardedUnaryGraph_restoreSymbol symbol buffer input stored)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (symbol::input))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons] using all

private def guardedUnaryGraphFlag (accepted : Bool) : GraphSymbol :=
  if accepted then Sum.inr none else Sum.inl none

private theorem guardedUnaryGraph_branchFlag (accepted : Bool) (stored : List GraphSymbol) :
    steinerGuardedUnaryGraphMachine.step (guardedUnaryGraphCfg (some .branchOnFlag) [] [guardedUnaryGraphFlag accepted] stored) =
      some (guardedUnaryGraphCfg (some (if accepted then .restoreWords else .discardWords)) [] [] stored) := by
  cases accepted <;> simp [FinTM2.step,steinerGuardedUnaryGraphMachine,guardedUnaryGraphCfg,Turing.TM2.step,Turing.TM2.stepAux,
    guardedUnaryGraphProgram,guardedUnaryGraphObserve,guardedUnaryGraphNext,guardedUnaryGraphFlag,guardedUnaryGraphPassed,
    guardedUnaryGraph_update4] <;> rfl

private theorem guardedUnaryGraph_restoreWordSymbol (symbol : GraphSymbol) (input stored : List GraphSymbol) :
    steinerGuardedUnaryGraphMachine.step (guardedUnaryGraphCfg (some .restoreWords) [] input (symbol::stored)) =
      some (guardedUnaryGraphCfg (some .restoreWords) [] (Sum.inr (guardedUnaryGraphRawBit symbol)::input) stored) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphMachine,guardedUnaryGraphCfg,Turing.TM2.step,Turing.TM2.stepAux,
    guardedUnaryGraphProgram,guardedUnaryGraphObserve,guardedUnaryGraphNext,guardedUnaryGraph_update4,guardedUnaryGraph_update6]
  rfl

private theorem guardedUnaryGraph_restoreWordEnd (input : List GraphSymbol) :
    steinerGuardedUnaryGraphMachine.step (guardedUnaryGraphCfg (some .restoreWords) [] input []) =
      some (guardedUnaryGraphCfg (some .skipBound) [] input []) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphMachine,guardedUnaryGraphCfg,Turing.TM2.step,Turing.TM2.stepAux,
    guardedUnaryGraphProgram,guardedUnaryGraphObserve,guardedUnaryGraphNext,guardedUnaryGraph_update6]
  rfl

private def guardedUnaryGraph_restoreWords (stored input : List GraphSymbol) :
    EvalsToInTime steinerGuardedUnaryGraphMachine.step (guardedUnaryGraphCfg (some .restoreWords) [] input stored)
      (some (guardedUnaryGraphCfg (some .skipBound) []
        (stored.reverse.map ((Sum.inr : Option Bool → GraphSymbol) ∘ guardedUnaryGraphRawBit)++input) [])) (stored.length+1) := by
  induction stored generalizing input with
  | nil => exact guardedUnaryGraph_one (guardedUnaryGraph_restoreWordEnd input)
  | cons symbol stored ih =>
    have first := guardedUnaryGraph_one (guardedUnaryGraph_restoreWordSymbol symbol input stored)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (Sum.inr (guardedUnaryGraphRawBit symbol)::input))
    simpa only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,Function.comp_apply,List.append_assoc,
      List.singleton_append,List.length_cons] using all

private theorem guardedUnaryGraph_skipBit (bit : Bool) (input : List GraphSymbol) :
    steinerGuardedUnaryGraphMachine.step
      (guardedUnaryGraphCfg (some .skipBound) [] (Sum.inr (some bit)::input) []) =
      some (guardedUnaryGraphCfg (some .skipBound) [] input []) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphMachine,guardedUnaryGraphCfg,Turing.TM2.step,Turing.TM2.stepAux,
    guardedUnaryGraphProgram,guardedUnaryGraphObserve,guardedUnaryGraphNext,guardedUnaryGraphIsWordBit,guardedUnaryGraph_update4]
  rfl

private theorem guardedUnaryGraph_skipDivider (input : List GraphSymbol) :
    steinerGuardedUnaryGraphMachine.step (guardedUnaryGraphCfg (some .skipBound) [] (Sum.inr none::input) []) =
      some (guardedUnaryGraphCfg (some (.decode steinerEndpointUnaryBatchMachine.main)) [] input []) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphMachine,guardedUnaryGraphCfg,Turing.TM2.step,Turing.TM2.stepAux,
    guardedUnaryGraphProgram,guardedUnaryGraphObserve,guardedUnaryGraphNext,guardedUnaryGraphIsWordBit,guardedUnaryGraph_update4]
  rfl

private def guardedUnaryGraph_skip (bound : List Bool) (input : List GraphSymbol) :
    EvalsToInTime steinerGuardedUnaryGraphMachine.step
      (guardedUnaryGraphCfg (some .skipBound) [] ((bound.map fun bit => Sum.inr (some bit))++Sum.inr none::input) [])
      (some (guardedUnaryGraphCfg (some (.decode steinerEndpointUnaryBatchMachine.main)) [] input [])) (bound.length+1) := by
  induction bound with
  | nil => exact guardedUnaryGraph_one (guardedUnaryGraph_skipDivider input)
  | cons bit bound ih =>
    have first := guardedUnaryGraph_one (guardedUnaryGraph_skipBit bit ((bound.map fun b => Sum.inr (some b))++Sum.inr none::input))
    have all := EvalsToInTime.trans _ _ _ _ _ _ first ih
    simpa only [List.map_cons,List.cons_append,List.length_cons] using all

private theorem guardedUnaryGraph_word (word : List Bool) :
    ((encodeSteinerSingleBoundWord word).map Sum.inl).map ((Sum.inr : Option Bool → GraphSymbol) ∘ guardedUnaryGraphRawBit) =
      (word.map some++[none]).map Sum.inr := by
  change (((word.map fun bit => some (some bit))++[some none]).map Sum.inl).map
      ((Sum.inr : Option Bool → GraphSymbol) ∘ guardedUnaryGraphRawBit) = (word.map some++[none]).map Sum.inr
  simp [List.map_map,Function.comp_def,guardedUnaryGraphRawBit]

private theorem guardedUnaryGraph_words (bound : List Bool) (words : List (List Bool)) :
    ((encodeSteinerSingleBound (bound,words)).map Sum.inl).map ((Sum.inr : Option Bool → GraphSymbol) ∘ guardedUnaryGraphRawBit) =
      (bound.map fun bit => Sum.inr (some bit))++Sum.inr none::(encodeSteinerBinaryEndpointWords words).map Sum.inr := by
  have tail : ((words.flatMap encodeSteinerSingleBoundWord).map Sum.inl).map ((Sum.inr : Option Bool → GraphSymbol) ∘ guardedUnaryGraphRawBit) =
      (encodeSteinerBinaryEndpointWords words).map Sum.inr := by
    induction words with
    | nil => rfl
    | cons word words ih =>
      change ((words.flatMap encodeSteinerSingleBoundWord).map Sum.inl).map ((Sum.inr : Option Bool → GraphSymbol) ∘ guardedUnaryGraphRawBit) =
        (encodeSteinerBinaryEndpointWords words).map Sum.inr at ih
      change ((encodeSteinerSingleBoundWord word++words.flatMap encodeSteinerSingleBoundWord).map Sum.inl).map
          ((Sum.inr : Option Bool → GraphSymbol) ∘ guardedUnaryGraphRawBit) =
        ((word.map some++[none])++encodeSteinerBinaryEndpointWords words).map Sum.inr
      simp only [List.map_append,guardedUnaryGraph_word,ih]
  change ((encodeSteinerSingleBoundWord bound++words.flatMap encodeSteinerSingleBoundWord).map Sum.inl).map
      ((Sum.inr : Option Bool → GraphSymbol) ∘ guardedUnaryGraphRawBit) = _
  simp only [List.map_append]
  rw [guardedUnaryGraph_word,tail]
  simp only [List.map_append,List.map_map,Function.comp_def,List.map_cons,List.map_nil,
    List.singleton_append,List.append_assoc]

private def guardedUnaryGraph_prepareDecode (bound : List Bool) (words : List (List Bool)) :
    EvalsToInTime steinerGuardedUnaryGraphMachine.step
      (guardedUnaryGraphCfg (some .restoreWords) [] [] ((encodeSteinerSingleBound (bound,words)).map Sum.inl).reverse)
      (some (guardedUnaryGraphCfg (some (.decode steinerEndpointUnaryBatchMachine.main)) []
        ((encodeSteinerBinaryEndpointWords words).map Sum.inr) []))
      ((encodeSteinerSingleBound (bound,words)).length+bound.length+2) := by
  have restored := guardedUnaryGraph_restoreWords ((encodeSteinerSingleBound (bound,words)).map Sum.inl).reverse []
  rw [List.reverse_reverse,List.append_nil,List.length_reverse,List.length_map,guardedUnaryGraph_words] at restored
  have all := EvalsToInTime.trans _ _ _ _ _ _ restored (guardedUnaryGraph_skip bound ((encodeSteinerBinaryEndpointWords words).map Sum.inr))
  exact ⟨all.toEvalsTo,by have spent := all.steps_le_m; omega⟩

private theorem guardedUnaryGraph_discardSymbol (symbol : GraphSymbol) (stored : List GraphSymbol) :
    steinerGuardedUnaryGraphMachine.step (guardedUnaryGraphCfg (some .discardWords) [] [] (symbol::stored)) =
      some (guardedUnaryGraphCfg (some .discardWords) [] [] stored) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphMachine,guardedUnaryGraphCfg,Turing.TM2.step,Turing.TM2.stepAux,
    guardedUnaryGraphProgram,guardedUnaryGraphObserve,guardedUnaryGraphNext,guardedUnaryGraph_update6]
  rfl

private theorem guardedUnaryGraph_discardEnd :
    steinerGuardedUnaryGraphMachine.step (guardedUnaryGraphCfg (some .discardWords) [] [] []) =
      some (guardedUnaryGraphCfg none [] [Sum.inl none] []) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphMachine,guardedUnaryGraphCfg,Turing.TM2.step,Turing.TM2.stepAux,
    guardedUnaryGraphProgram,guardedUnaryGraphObserve,guardedUnaryGraph_update4,guardedUnaryGraph_update6]
  rfl

private def guardedUnaryGraph_discard (stored : List GraphSymbol) :
    EvalsToInTime steinerGuardedUnaryGraphMachine.step
      (guardedUnaryGraphCfg (some .discardWords) [] [] stored)
      (some (guardedUnaryGraphCfg none [] [Sum.inl none] [])) (stored.length+1) := by
  induction stored with
  | nil => exact guardedUnaryGraph_one guardedUnaryGraph_discardEnd
  | cons symbol stored ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _ (guardedUnaryGraph_one (guardedUnaryGraph_discardSymbol symbol stored)) ih
    simpa only [List.length_cons] using all

private def guardedUnaryGraphCheckPassive (stored : List GraphSymbol) (i : Fin 7) : List GraphSymbol :=
  if i = 6 then stored else []

private noncomputable def guardedUnaryGraphCheckTranslated (stored : List GraphSymbol)
    (c : steinerSingleBoundStartupMachine.Cfg) : steinerGuardedUnaryGraphMachine.Cfg :=
  StackIndexEmbedding.configuration guardedUnaryGraphCheckSlots (guardedUnaryGraphCheckPassive stored)
    (guardedUnaryGraphCheckTag.returningConfiguration .branchOnFlag c)

private theorem guardedUnaryGraph_checkStep (stored : List GraphSymbol) {c after : steinerSingleBoundStartupMachine.Cfg}
    (step : steinerSingleBoundStartupMachine.step c = some after) :
    steinerGuardedUnaryGraphMachine.step (guardedUnaryGraphCheckTranslated stored c) =
      some (guardedUnaryGraphCheckTranslated stored after) := by
  have tagged := guardedUnaryGraphCheckTag.step_embedded_return .branchOnFlag (base := steinerSingleBoundStartupMachine.m)
    (host := guardedUnaryGraphGuardInner) (fun _ => rfl) step
  have framed := StackIndexEmbedding.step_on guardedUnaryGraphCheckSlots (base := guardedUnaryGraphGuardInner)
    (guardedUnaryGraphCheckPassive stored) (guardedUnaryGraphCheckTag.returningConfiguration .branchOnFlag c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem guardedUnaryGraph_checkTapes (stored : List GraphSymbol) (c : steinerSingleBoundStartupMachine.Cfg)
    (input : List GraphSymbol) (tapes : c.stk = ![[],[],[],[],input]) :
    (guardedUnaryGraphCheckTranslated stored c).stk = ![[],[],[],[],input,[],stored] := by
  have image (i : Fin 5) : (guardedUnaryGraphCheckTranslated stored c).stk (guardedUnaryGraphCheckSlots i) =
      (![[],[],[],[],input] : Fin 5 → List GraphSymbol) i := by
    change StackIndexEmbedding.tapesAt guardedUnaryGraphCheckSlots (fun i => (c.stk i).map id) _
      (guardedUnaryGraphCheckSlots i) = _
    rw [StackIndexEmbedding.tapesAt_image,List.map_id_fun,tapes]
    rfl
  have extra (i : Fin 7) (outside : ∀ j, guardedUnaryGraphCheckSlots j ≠ i) :
      (guardedUnaryGraphCheckTranslated stored c).stk i = guardedUnaryGraphCheckPassive stored i := by
    change StackIndexEmbedding.tapesAt guardedUnaryGraphCheckSlots _ _ i = _
    exact StackIndexEmbedding.tapesAt_extra _ _ _ outside
  funext i
  fin_cases i
  · exact image 0
  · exact image 1
  · exact image 2
  · exact image 3
  · exact image 4
  · exact extra 5 (by intro j; fin_cases j <;> decide)
  · exact extra 6 (by intro j; fin_cases j <;> decide)

private theorem guardedUnaryGraph_checkInit (input stored : List GraphSymbol) :
    guardedUnaryGraphCheckTranslated stored (initList steinerSingleBoundStartupMachine input) =
      guardedUnaryGraphCfg (some (.guard steinerSingleBoundStartupMachine.main)) [] input stored := by
  apply congrArg (fun stk : Fin 7 → List GraphSymbol =>
    (⟨some (.guard steinerSingleBoundStartupMachine.main),guardedUnaryGraphInitial,stk⟩ : steinerGuardedUnaryGraphMachine.Cfg))
  exact guardedUnaryGraph_checkTapes stored (initList steinerSingleBoundStartupMachine input) input (by
    funext i
    fin_cases i <;> rfl)

private theorem guardedUnaryGraph_checkReturn (output stored : List GraphSymbol) :
    guardedUnaryGraphCheckTranslated stored (haltList steinerSingleBoundStartupMachine output) =
      guardedUnaryGraphCfg (some .branchOnFlag) [] output stored := by
  apply congrArg (fun stk : Fin 7 → List GraphSymbol =>
    (⟨some .branchOnFlag,guardedUnaryGraphInitial,stk⟩ : steinerGuardedUnaryGraphMachine.Cfg))
  exact guardedUnaryGraph_checkTapes stored (haltList steinerSingleBoundStartupMachine output) output (by
    funext i
    fin_cases i <;> rfl)

private def guardedUnaryGraph_checkEval (input output stored : List GraphSymbol) {bound : ℕ}
    (run : TM2OutputsInTime steinerSingleBoundStartupMachine input (some output) bound) :
    EvalsToInTime steinerGuardedUnaryGraphMachine.step
      (guardedUnaryGraphCfg (some (.guard steinerSingleBoundStartupMachine.main)) [] input stored)
      (some (guardedUnaryGraphCfg (some .branchOnFlag) [] output stored)) bound := by
  refine ⟨⟨run.steps,?_⟩,run.steps_le_m⟩
  have all := iterate_map_some (guardedUnaryGraphCheckTranslated stored) (fun step => guardedUnaryGraph_checkStep stored step)
    run.steps run.evals_in_steps
  change (flip bind steinerGuardedUnaryGraphMachine.step)^[run.steps]
      (some (guardedUnaryGraphCheckTranslated stored (initList steinerSingleBoundStartupMachine input))) =
    some (guardedUnaryGraphCheckTranslated stored (haltList steinerSingleBoundStartupMachine output)) at all
  rw [guardedUnaryGraph_checkInit,guardedUnaryGraph_checkReturn] at all
  exact all

private theorem guardedUnaryGraph_emptySeedInput (graph : SteinerSingleBoundInput) :
    encodeSteinerSingleBoundStartup (graph,(0,[])) = (encodeSteinerSingleBound graph).map Sum.inl := by
  simp [encodeSteinerSingleBoundStartup,encodeSteinerSeedTapeRequest]

private theorem guardedUnaryGraph_emptySeedAnswer (graph : SteinerSingleBoundInput) :
    steinerSingleBoundStartupAnswer (graph,(0,[])) =
      [guardedUnaryGraphFlag (steinerRangeChecks (expandSteinerSingleBound graph))] := by
  have emptyFrame : encodeSteinerSeedTapeRequest (0,[]) = [] := rfl
  have zeroSeed : splitSteinerSeedTapeOrReject (0,[]) = [none] := rfl
  cases accepted : steinerRangeChecks (expandSteinerSingleBound graph) <;>
    simp [steinerSingleBoundStartupAnswer,steinerRawRangeSeedAnswer,encodeSteinerRawRangeSeedAnswer,
      emptyFrame,zeroSeed,accepted,guardedUnaryGraphFlag]

private def guardedUnaryGraph_checkRun (graph : SteinerSingleBoundInput) :
    TM2OutputsInTime steinerSingleBoundStartupMachine ((encodeSteinerSingleBound graph).map Sum.inl)
      (some [guardedUnaryGraphFlag (steinerRangeChecks (expandSteinerSingleBound graph))])
      (2*(encodeSteinerSingleBound graph).length+
        8*(encodeSteinerRawRangeBatch (expandSteinerSingleBound graph)).length+3*graph.1.length+12) := by
  have run := steinerSingleBoundStartupMachine_run (graph,(0,[]))
  simpa only [guardedUnaryGraph_emptySeedInput,guardedUnaryGraph_emptySeedAnswer,Prod.fst,Prod.snd,Nat.mul_zero,Nat.add_zero] using run

private def guardedUnaryGraph_rejectedCheckRun (graph : SteinerSingleBoundInput)
    (rejected : steinerRangeChecks (expandSteinerSingleBound graph) = false) :
    TM2OutputsInTime steinerSingleBoundStartupMachine ((encodeSteinerSingleBound graph).map Sum.inl)
      (some [guardedUnaryGraphFlag false])
      (2*(encodeSteinerSingleBound graph).length+
        8*(encodeSteinerRawRangeBatch (expandSteinerSingleBound graph)).length+3*graph.1.length+9) := by
  have run := steinerSingleBoundStartupMachine_rejectedGraph (graph,(0,[])) rejected
  simpa [guardedUnaryGraph_emptySeedInput,guardedUnaryGraphFlag,encodeSteinerSeedTapeRequest] using run

private def guardedUnaryGraph_check (frame : List GraphSymbol) (accepted : Bool) {bound : ℕ}
    (run : TM2OutputsInTime steinerSingleBoundStartupMachine frame (some [guardedUnaryGraphFlag accepted]) bound) :
    EvalsToInTime steinerGuardedUnaryGraphMachine.step (guardedUnaryGraphCfg (some .save) [] frame [])
      (some (guardedUnaryGraphCfg (some (if accepted then .restoreWords else .discardWords)) [] [] frame.reverse))
      (2*frame.length+bound+3) := by
  have saved := guardedUnaryGraph_save frame [] []
  simp only [List.append_nil] at saved
  have restored := guardedUnaryGraph_restore frame.reverse [] frame.reverse
  rw [List.reverse_reverse,List.append_nil,List.length_reverse] at restored
  have start := EvalsToInTime.trans _ _ _ _ _ _ saved restored
  have after := EvalsToInTime.trans _ _ _ _ _ _ start (guardedUnaryGraph_checkEval frame _ frame.reverse run)
  have all := EvalsToInTime.trans _ _ _ _ _ _ after (guardedUnaryGraph_one (guardedUnaryGraph_branchFlag accepted frame.reverse))
  exact ⟨all.toEvalsTo,by have paid := all.steps_le_m; omega⟩

private noncomputable def guardedUnaryGraphDecodeTranslated (c : steinerEndpointUnaryBatchMachine.Cfg) :
    steinerGuardedUnaryGraphMachine.Cfg :=
  guardedUnaryGraphDecodeTag.configuration (StackIndexEmbedding.configuration guardedUnaryGraphDecodeSlots (fun _ => []) c)

private theorem guardedUnaryGraph_decodeTapes (c : steinerEndpointUnaryBatchMachine.Cfg) (word : List (Option Bool))
    (tapes : c.stk = ![[],[],[],[],word,[]]) :
    (guardedUnaryGraphDecodeTranslated c).stk = ![[],[],[],[],word.map Sum.inr,[],[]] := by
  have image (i : Fin 6) : (guardedUnaryGraphDecodeTranslated c).stk (guardedUnaryGraphDecodeSlots i) =
      ((![[],[],[],[],word,[]] : Fin 6 → List (Option Bool)) i).map Sum.inr := by
    change (StackIndexEmbedding.tapesAt guardedUnaryGraphDecodeSlots c.stk (fun _ => []) (guardedUnaryGraphDecodeSlots i)).map Sum.inr = _
    rw [StackIndexEmbedding.tapesAt_image,tapes]
  funext i
  fin_cases i
  · exact image 0
  · exact image 1
  · exact image 2
  · exact image 3
  · exact image 4
  · exact image 5
  · have outside (j : Fin 6) : guardedUnaryGraphDecodeSlots j ≠ 6 := by
      fin_cases j <;> decide
    change (StackIndexEmbedding.tapesAt guardedUnaryGraphDecodeSlots _ (fun _ => []) 6).map Sum.inr = []
    rw [StackIndexEmbedding.tapesAt_extra _ _ _ outside]
    rfl

private theorem guardedUnaryGraph_decodeInit (input : List (Option Bool)) :
    guardedUnaryGraphDecodeTranslated (initList steinerEndpointUnaryBatchMachine input) =
      guardedUnaryGraphCfg (some (.decode steinerEndpointUnaryBatchMachine.main)) [] (input.map Sum.inr) [] := by
  apply congrArg (fun stk : Fin 7 → List GraphSymbol =>
    (⟨some (.decode steinerEndpointUnaryBatchMachine.main),guardedUnaryGraphInitial,stk⟩ : steinerGuardedUnaryGraphMachine.Cfg))
  exact guardedUnaryGraph_decodeTapes (initList steinerEndpointUnaryBatchMachine input) input (by
    funext i
    fin_cases i <;> rfl)

private theorem guardedUnaryGraph_decodeHalt (out : List (Option Bool)) :
    guardedUnaryGraphDecodeTranslated (haltList steinerEndpointUnaryBatchMachine out) =
      guardedUnaryGraphCfg none [] (out.map Sum.inr) [] := by
  apply congrArg (fun stk : Fin 7 → List GraphSymbol =>
    (⟨none,guardedUnaryGraphInitial,stk⟩ : steinerGuardedUnaryGraphMachine.Cfg))
  exact guardedUnaryGraph_decodeTapes (haltList steinerEndpointUnaryBatchMachine out) out (by
    funext i
    fin_cases i <;> rfl)

private def guardedUnaryGraph_decode (input out : List (Option Bool)) {bound : ℕ}
    (run : TM2OutputsInTime steinerEndpointUnaryBatchMachine input (some out) bound) :
    EvalsToInTime steinerGuardedUnaryGraphMachine.step
      (guardedUnaryGraphCfg (some (.decode steinerEndpointUnaryBatchMachine.main)) [] (input.map Sum.inr) [])
      (some (guardedUnaryGraphCfg none [] (out.map Sum.inr) [])) bound := by
  refine ⟨⟨run.steps,?_⟩,run.steps_le_m⟩
  let framed := StackIndexEmbedding.evaluation guardedUnaryGraphDecodeSlots (base := steinerEndpointUnaryBatchMachine.m)
    (fun _ => []) run
  let tagged := guardedUnaryGraphDecodeTag.evaluation (base := guardedUnaryGraphDecodeFramed)
    (host := guardedUnaryGraphProgram) (fun _ => rfl) framed
  have evaluated : (flip bind steinerGuardedUnaryGraphMachine.step)^[run.steps]
      (some (guardedUnaryGraphDecodeTranslated (initList steinerEndpointUnaryBatchMachine input))) =
    some (guardedUnaryGraphDecodeTranslated (haltList steinerEndpointUnaryBatchMachine out)) := tagged.evals_in_steps
  rw [guardedUnaryGraph_decodeInit,guardedUnaryGraph_decodeHalt] at evaluated
  exact evaluated

private theorem guardedUnaryGraph_init (input : List GraphSymbol) :
    initList steinerGuardedUnaryGraphMachine input = guardedUnaryGraphCfg (some .save) [] input [] := by
  apply congrArg (fun stk : Fin 7 → List GraphSymbol =>
    (⟨some .save,guardedUnaryGraphInitial,stk⟩ : steinerGuardedUnaryGraphMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem guardedUnaryGraph_halt (out : List GraphSymbol) :
    haltList steinerGuardedUnaryGraphMachine out = guardedUnaryGraphCfg none [] out [] := by
  apply congrArg (fun stk : Fin 7 → List GraphSymbol =>
    (⟨none,guardedUnaryGraphInitial,stk⟩ : steinerGuardedUnaryGraphMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- Supply one bound word and then the graph endpoints in row order. -/
def encodeSteinerGuardedUnaryGraph (bound : List Bool) (rows : List SteinerRangeWordPair) : List SteinerRawRangeSeedSymbol :=
  (encodeSteinerSingleBound (bound,steinerRawGraphEndpointWords rows)).map Sum.inl

private theorem guardedUnaryGraph_rangeFlag {n : ℕ} (bound : List Bool) (number : binaryWordValue bound = n)
    (rows : List SteinerRangeWordPair) :
    steinerRangeChecks (expandSteinerSingleBound (bound,steinerRawGraphEndpointWords rows)) =
      (decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1.isSome := by
  rw [show expandSteinerSingleBound (bound,steinerRawGraphEndpointWords rows) = steinerRangeRequests bound rows
    from expandSteinerSingleBound_graph bound rows,steinerRangeRequests_guarded_flag bound number rows]

/-- The machine returns the exact finite endpoints on graph acceptance. -/
def steinerGuardedUnaryGraphMachine_accepted {n : ℕ} (bound : List Bool) (number : binaryWordValue bound = n)
    (rows : List SteinerRangeWordPair) (decoded : List (Fin n × Fin n))
    (accepted : (decodeCheckedBinaryFinArcRowsWithWork (n+binaryEndpointBits rows) rows).1 = some decoded) :
    let graph : SteinerSingleBoundInput := (bound,steinerRawGraphEndpointWords rows)
    TM2OutputsInTime steinerGuardedUnaryGraphMachine (encodeSteinerGuardedUnaryGraph bound rows)
      (some ((encodeSteinerUnaryEndpointValues (decoded.flatMap fun e => [e.1.val,e.2.val])).map Sum.inr))
      (5*(encodeSteinerSingleBound graph).length+
        8*(encodeSteinerRawRangeBatch (expandSteinerSingleBound graph)).length+
        4*bound.length+4*binaryEndpointBits rows+8*rows.length+10*(rows.length*n)+19) := by
  dsimp only
  let graph : SteinerSingleBoundInput := (bound,steinerRawGraphEndpointWords rows)
  let frame := encodeSteinerGuardedUnaryGraph bound rows
  have validFlag : steinerRangeChecks (expandSteinerSingleBound graph) = true := by
    rw [guardedUnaryGraph_rangeFlag bound number rows,accepted]
    rfl
  have check := guardedUnaryGraph_check frame _ (guardedUnaryGraph_checkRun graph)
  simp only [validFlag,ite_true] at check
  have prepared := guardedUnaryGraph_prepareDecode bound (steinerRawGraphEndpointWords rows)
  have placed := EvalsToInTime.trans _ _ _ _ _ _ check prepared
  have decodeRun := steinerEndpointUnaryBatchMachine_guardedGraph (n+binaryEndpointBits rows) rows decoded accepted
  have all := EvalsToInTime.trans _ _ _ _ _ _ placed (guardedUnaryGraph_decode _ _ decodeRun)
  change EvalsToInTime steinerGuardedUnaryGraphMachine.step _ (some (haltList steinerGuardedUnaryGraphMachine _)) _
  rw [guardedUnaryGraph_init,guardedUnaryGraph_halt]
  refine ⟨all.toEvalsTo,?_⟩
  have paid := all.steps_le_m
  dsimp only [frame,graph,encodeSteinerGuardedUnaryGraph] at paid
  simp only [List.length_map] at paid
  omega

/-- Rejection clears the saved graph and returns its marker within
a bound depending only on the binary frame lengths. -/
def steinerGuardedUnaryGraphMachine_rejected {n : ℕ} (bound : List Bool) (number : binaryWordValue bound = n)
    (rows : List SteinerRangeWordPair)
    (rejected : (decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1 = none) :
    let graph : SteinerSingleBoundInput := (bound,steinerRawGraphEndpointWords rows)
    TM2OutputsInTime steinerGuardedUnaryGraphMachine (encodeSteinerGuardedUnaryGraph bound rows)
      (some [Sum.inl none])
      (5*(encodeSteinerSingleBound graph).length+
        8*(encodeSteinerRawRangeBatch (expandSteinerSingleBound graph)).length+3*bound.length+13) := by
  dsimp only
  let graph : SteinerSingleBoundInput := (bound,steinerRawGraphEndpointWords rows)
  let frame := encodeSteinerGuardedUnaryGraph bound rows
  have flag : steinerRangeChecks (expandSteinerSingleBound graph) = false := by
    rw [guardedUnaryGraph_rangeFlag bound number rows,rejected]
    rfl
  have check := guardedUnaryGraph_check frame false (guardedUnaryGraph_rejectedCheckRun graph flag)
  have all := EvalsToInTime.trans _ _ _ _ _ _ check (guardedUnaryGraph_discard frame.reverse)
  change EvalsToInTime steinerGuardedUnaryGraphMachine.step _ (some (haltList steinerGuardedUnaryGraphMachine _)) _
  rw [guardedUnaryGraph_init,guardedUnaryGraph_halt]
  refine ⟨all.toEvalsTo,?_⟩
  have paid := all.steps_le_m
  dsimp only [frame,graph,encodeSteinerGuardedUnaryGraph] at paid
  simp only [List.length_reverse,List.length_map] at paid
  omega

/-- Use the count encoded by the bound word. All output indices carry
the right tag, and a rejected frame returns the left-tagged marker. -/
def steinerGuardedUnaryGraphAnswer (bound : List Bool) (rows : List SteinerRangeWordPair) : List SteinerRawRangeSeedSymbol :=
  let n := binaryWordValue bound
  match (decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1 with
  | none => [Sum.inl none]
  | some decoded => (encodeSteinerUnaryEndpointValues (decoded.flatMap fun e => [e.1.val,e.2.val])).map Sum.inr

/-- The machine implements both outcomes described by the guarded decoder. -/
def steinerGuardedUnaryGraphMachine_run (bound : List Bool) (rows : List SteinerRangeWordPair) :
    let graph : SteinerSingleBoundInput := (bound,steinerRawGraphEndpointWords rows)
    TM2OutputsInTime steinerGuardedUnaryGraphMachine (encodeSteinerGuardedUnaryGraph bound rows)
      (some (steinerGuardedUnaryGraphAnswer bound rows))
      (5*(encodeSteinerSingleBound graph).length+
        8*(encodeSteinerRawRangeBatch (expandSteinerSingleBound graph)).length+4*bound.length+
        4*binaryEndpointBits rows+8*rows.length+10*(rows.length*binaryWordValue bound)+19) := by
  dsimp only
  unfold steinerGuardedUnaryGraphAnswer
  dsimp only
  cases result : (decodeCheckedBinaryFinArcRowsWithWork (n := binaryWordValue bound)
      (binaryWordValue bound+binaryEndpointBits rows) rows).1 with
  | none =>
    have run := steinerGuardedUnaryGraphMachine_rejected bound rfl rows result
    exact ⟨run.toEvalsTo,run.steps_le_m.trans (by omega)⟩
  | some decoded =>
    exact steinerGuardedUnaryGraphMachine_accepted bound rfl rows decoded result

/-- The original frame has one divider for the bound and one per
endpoint, in addition to every supplied bit. -/
theorem encodeSteinerGuardedUnaryGraph_length (bound : List Bool) (rows : List SteinerRangeWordPair) :
    (encodeSteinerGuardedUnaryGraph bound rows).length = bound.length+1+(binaryEndpointBits rows+2*rows.length) := by
  unfold encodeSteinerGuardedUnaryGraph
  rw [List.length_map,encodeSteinerSingleBound_length,steinerRawGraphEndpointWords_bits,steinerRawGraphEndpointWords_length]

/-- The total decoding bound is polynomial in the original binary
frame length and the numerical vertex count. -/
def steinerGuardedUnaryGraphMachine_vertex_time (bound : List Bool) (rows : List SteinerRangeWordPair) :
    let x := (encodeSteinerGuardedUnaryGraph bound rows).length
    TM2OutputsInTime steinerGuardedUnaryGraphMachine (encodeSteinerGuardedUnaryGraph bound rows)
      (some (steinerGuardedUnaryGraphAnswer bound rows)) (8*x^2+21*x+10*(x*binaryWordValue bound)+19) := by
  dsimp only
  let graph : SteinerSingleBoundInput := (bound,steinerRawGraphEndpointWords rows)
  let x := (encodeSteinerGuardedUnaryGraph bound rows).length
  let y := (encodeSteinerRawRangeBatch (expandSteinerSingleBound graph)).length
  have frame : x = (encodeSteinerSingleBound graph).length := by
    simp [x,graph,encodeSteinerGuardedUnaryGraph]
  have layout : x = bound.length+1+(binaryEndpointBits rows+2*rows.length) :=
    encodeSteinerGuardedUnaryGraph_length bound rows
  have expanded : y ≤ x+x^2 := by rw [frame]; exact encodeSteinerSingleBound_expanded_le graph
  have rowFits : rows.length ≤ x := by omega
  have vertexFits := Nat.mul_le_mul_right (binaryWordValue bound) rowFits
  have fits : 5*(encodeSteinerSingleBound graph).length+8*y+4*bound.length+4*binaryEndpointBits rows+
      8*rows.length+10*(rows.length*binaryWordValue bound)+19 ≤ 8*x^2+21*x+10*(x*binaryWordValue bound)+19 := by
    omega
  have run := steinerGuardedUnaryGraphMachine_run bound rows
  exact ⟨run.toEvalsTo,run.steps_le_m.trans fits⟩

/-- Rejection is quadratic in the original frame length, independently
of the numerical size of its bound. -/
def steinerGuardedUnaryGraphMachine_rejected_time {n : ℕ} (bound : List Bool) (number : binaryWordValue bound = n)
    (rows : List SteinerRangeWordPair)
    (rejected : (decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1 = none) :
    let x := (encodeSteinerGuardedUnaryGraph bound rows).length
    TM2OutputsInTime steinerGuardedUnaryGraphMachine (encodeSteinerGuardedUnaryGraph bound rows)
      (some [Sum.inl none]) (8*x^2+16*x+13) := by
  dsimp only
  let graph : SteinerSingleBoundInput := (bound,steinerRawGraphEndpointWords rows)
  let x := (encodeSteinerGuardedUnaryGraph bound rows).length
  let y := (encodeSteinerRawRangeBatch (expandSteinerSingleBound graph)).length
  have frame : x = (encodeSteinerSingleBound graph).length := by
    simp [x,graph,encodeSteinerGuardedUnaryGraph]
  have layout : x = bound.length+1+(binaryEndpointBits rows+2*rows.length) :=
    encodeSteinerGuardedUnaryGraph_length bound rows
  have expanded : y ≤ x+x^2 := by rw [frame]; exact encodeSteinerSingleBound_expanded_le graph
  have fits : 5*(encodeSteinerSingleBound graph).length+8*y+3*bound.length+13 ≤ 8*x^2+16*x+13 := by omega
  have run := steinerGuardedUnaryGraphMachine_rejected bound number rows rejected
  exact ⟨run.toEvalsTo,run.steps_le_m.trans fits⟩

end OnlineReachabilityPreservers
