import OnlineReachabilityPreservers.SteinerRawRangeBatchMachine

/-! Expand a single binary bound into the raw range requests of multiple endpoint words. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private inductive OneBoundLabel where
  | loadBound
  | restoreBound
  | endpoint
  | copyBound
  | clearBound
  | finish
  deriving DecidableEq

private instance : Fintype OneBoundLabel where
  elems := {.loadBound,.restoreBound,.endpoint,.copyBound,.clearBound,.finish}
  complete := by intro label; cases label <;> simp

private abbrev OneBoundRegister := Option SteinerRawRangeSymbol
private abbrev OneBoundProgram :=
  Turing.TM2.Stmt (fun _ : Fin 4 => SteinerRawRangeSymbol) OneBoundLabel OneBoundRegister

private def oneBoundObserve (_ : OneBoundRegister) (seen : Option SteinerRawRangeSymbol) : OneBoundRegister := seen

private def oneBoundProgram : OneBoundLabel → OneBoundProgram
  | .loadBound =>
    pop 0 oneBoundObserve <|
      branch (fun r => r.join.join.isSome)
        (push 2 (·.getD none) <| load (fun _ => none) (goto (fun _ => .loadBound)))
        (load (fun _ => none) (goto (fun _ => .restoreBound)))
  | .restoreBound =>
    pop 2 oneBoundObserve <|
      branch Option.isSome
        (push 1 (·.getD none) <| load (fun _ => none) (goto (fun _ => .restoreBound)))
        (load (fun _ => none) (goto (fun _ => .endpoint)))
  | .endpoint =>
    pop 0 oneBoundObserve <|
      branch Option.isSome
        (branch (fun r => r.join.join.isSome)
          (push 3 (·.getD none) <| load (fun _ => none) (goto (fun _ => .endpoint)))
          (push 3 (fun _ => some none) <| load (fun _ => none) (goto (fun _ => .copyBound))))
        (load (fun _ => none) (goto (fun _ => .clearBound)))
  | .copyBound =>
    pop 1 oneBoundObserve <|
      branch Option.isSome
        (push 3 (·.getD none) <| push 2 (·.getD none) <| load (fun _ => none) (goto (fun _ => .copyBound)))
        (push 3 (fun _ => none) <| load (fun _ => none) (goto (fun _ => .restoreBound)))
  | .clearBound =>
    pop 1 oneBoundObserve <|
      branch Option.isSome (load (fun _ => none) (goto (fun _ => .clearBound)))
        (load (fun _ => none) (goto (fun _ => .finish)))
  | .finish =>
    pop 3 oneBoundObserve <|
      branch Option.isSome
        (push 0 (·.getD none) <| load (fun _ => none) (goto (fun _ => .finish)))
        (load (fun _ => none) halt)

/-- Read the bound once. For each framed endpoint, copy the endpoint
and the stored bound into a comparison frame. -/
abbrev steinerOneBoundRangeMachine : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 0
  Γ _ := SteinerRawRangeSymbol
  Λ := OneBoundLabel
  main := .loadBound
  σ := OneBoundRegister
  initialState := none
  m := oneBoundProgram

private def oneBoundBits (word : List Bool) : List SteinerRawRangeSymbol :=
  word.map (fun bit => some (some bit))

/-- A word ends at the inner divider, including an empty word. -/
def encodeSteinerSingleBoundWord (word : List Bool) : List SteinerRawRangeSymbol :=
  oneBoundBits word ++ [some none]

abbrev SteinerSingleBoundInput := List Bool × List (List Bool)

/-- A binary bound is supplied once, followed by the framed endpoints. -/
def encodeSteinerSingleBound (request : SteinerSingleBoundInput) : List SteinerRawRangeSymbol :=
  encodeSteinerSingleBoundWord request.1 ++ request.2.flatMap encodeSteinerSingleBoundWord

def expandSteinerSingleBound (request : SteinerSingleBoundInput) : List SteinerRangeWordPair :=
  request.2.map (fun endpoint => (endpoint,request.1))

private def oneBoundCfg (label : Option OneBoundLabel)
    (input bound reversed output : List SteinerRawRangeSymbol) : steinerOneBoundRangeMachine.Cfg where
  l := label
  var := none
  stk := ![input,bound,reversed,output]

private theorem oneBound_update0 (i b r o next : List SteinerRawRangeSymbol) :
    Function.update (![i,b,r,o] : Fin 4 → List SteinerRawRangeSymbol) 0 next = ![next,b,r,o] := by
  funext slot
  fin_cases slot <;> simp [Function.update]

private theorem oneBound_update1 (i b r o next : List SteinerRawRangeSymbol) :
    Function.update (![i,b,r,o] : Fin 4 → List SteinerRawRangeSymbol) 1 next = ![i,next,r,o] := by
  funext slot
  fin_cases slot <;> simp [Function.update]

private theorem oneBound_update2 (i b r o next : List SteinerRawRangeSymbol) :
    Function.update (![i,b,r,o] : Fin 4 → List SteinerRawRangeSymbol) 2 next = ![i,b,next,o] := by
  funext slot
  fin_cases slot <;> simp [Function.update]

private theorem oneBound_update3 (i b r o next : List SteinerRawRangeSymbol) :
    Function.update (![i,b,r,o] : Fin 4 → List SteinerRawRangeSymbol) 3 next = ![i,b,r,next] := by
  funext slot
  fin_cases slot <;> simp [Function.update]

private theorem oneBound_loadBit (bit : Bool) (tail reversed : List SteinerRawRangeSymbol) :
    steinerOneBoundRangeMachine.step (oneBoundCfg (some .loadBound) (some (some bit)::tail) [] reversed []) =
      some (oneBoundCfg (some .loadBound) tail [] (some (some bit)::reversed) []) := by
  simp [FinTM2.step,steinerOneBoundRangeMachine,oneBoundCfg,Turing.TM2.step,Turing.TM2.stepAux,
    oneBoundProgram,oneBoundObserve,oneBound_update0,oneBound_update2]
  rfl

private theorem oneBound_loadDone (tail reversed : List SteinerRawRangeSymbol) :
    steinerOneBoundRangeMachine.step (oneBoundCfg (some .loadBound) (some none::tail) [] reversed []) =
      some (oneBoundCfg (some .restoreBound) tail [] reversed []) := by
  simp [FinTM2.step,steinerOneBoundRangeMachine,oneBoundCfg,Turing.TM2.step,Turing.TM2.stepAux,
    oneBoundProgram,oneBoundObserve,oneBound_update0]
  rfl

private theorem oneBound_restoreBoundSymbol (symbol : SteinerRawRangeSymbol) (i b r o : List SteinerRawRangeSymbol) :
    steinerOneBoundRangeMachine.step (oneBoundCfg (some .restoreBound) i b (symbol::r) o) =
      some (oneBoundCfg (some .restoreBound) i (symbol::b) r o) := by
  simp [FinTM2.step,steinerOneBoundRangeMachine,oneBoundCfg,Turing.TM2.step,Turing.TM2.stepAux,
    oneBoundProgram,oneBoundObserve,oneBound_update1,oneBound_update2]
  rfl

private theorem oneBound_restoreBoundDone (i b o : List SteinerRawRangeSymbol) :
    steinerOneBoundRangeMachine.step (oneBoundCfg (some .restoreBound) i b [] o) =
      some (oneBoundCfg (some .endpoint) i b [] o) := by
  simp [FinTM2.step,steinerOneBoundRangeMachine,oneBoundCfg,Turing.TM2.step,Turing.TM2.stepAux,
    oneBoundProgram,oneBoundObserve,oneBound_update2]
  rfl

private theorem oneBound_endpointBit (bit : Bool) (i b o : List SteinerRawRangeSymbol) :
    steinerOneBoundRangeMachine.step (oneBoundCfg (some .endpoint) (some (some bit)::i) b [] o) =
      some (oneBoundCfg (some .endpoint) i b [] (some (some bit)::o)) := by
  simp [FinTM2.step,steinerOneBoundRangeMachine,oneBoundCfg,Turing.TM2.step,Turing.TM2.stepAux,
    oneBoundProgram,oneBoundObserve,oneBound_update0,oneBound_update3]
  rfl

private theorem oneBound_endpointDone (i b o : List SteinerRawRangeSymbol) :
    steinerOneBoundRangeMachine.step (oneBoundCfg (some .endpoint) (some none::i) b [] o) =
      some (oneBoundCfg (some .copyBound) i b [] (some none::o)) := by
  simp [FinTM2.step,steinerOneBoundRangeMachine,oneBoundCfg,Turing.TM2.step,Turing.TM2.stepAux,
    oneBoundProgram,oneBoundObserve,oneBound_update0,oneBound_update3]
  rfl

private theorem oneBound_endpointsDone (b o : List SteinerRawRangeSymbol) :
    steinerOneBoundRangeMachine.step (oneBoundCfg (some .endpoint) [] b [] o) =
      some (oneBoundCfg (some .clearBound) [] b [] o) := by
  simp [FinTM2.step,steinerOneBoundRangeMachine,oneBoundCfg,Turing.TM2.step,Turing.TM2.stepAux,
    oneBoundProgram,oneBoundObserve,oneBound_update0]
  rfl

private theorem oneBound_copySymbol (symbol : SteinerRawRangeSymbol) (i b r o : List SteinerRawRangeSymbol) :
    steinerOneBoundRangeMachine.step (oneBoundCfg (some .copyBound) i (symbol::b) r o) =
      some (oneBoundCfg (some .copyBound) i b (symbol::r) (symbol::o)) := by
  simp [FinTM2.step,steinerOneBoundRangeMachine,oneBoundCfg,Turing.TM2.step,Turing.TM2.stepAux,
    oneBoundProgram,oneBoundObserve,oneBound_update1,oneBound_update2,oneBound_update3]
  rfl

private theorem oneBound_copyDone (i r o : List SteinerRawRangeSymbol) :
    steinerOneBoundRangeMachine.step (oneBoundCfg (some .copyBound) i [] r o) =
      some (oneBoundCfg (some .restoreBound) i [] r (none::o)) := by
  simp [FinTM2.step,steinerOneBoundRangeMachine,oneBoundCfg,Turing.TM2.step,Turing.TM2.stepAux,
    oneBoundProgram,oneBoundObserve,oneBound_update1,oneBound_update3]
  rfl

private theorem oneBound_clearSymbol (symbol : SteinerRawRangeSymbol) (b o : List SteinerRawRangeSymbol) :
    steinerOneBoundRangeMachine.step (oneBoundCfg (some .clearBound) [] (symbol::b) [] o) =
      some (oneBoundCfg (some .clearBound) [] b [] o) := by
  simp [FinTM2.step,steinerOneBoundRangeMachine,oneBoundCfg,Turing.TM2.step,Turing.TM2.stepAux,
    oneBoundProgram,oneBoundObserve,oneBound_update1]
  rfl

private theorem oneBound_clearDone (o : List SteinerRawRangeSymbol) :
    steinerOneBoundRangeMachine.step (oneBoundCfg (some .clearBound) [] [] [] o) =
      some (oneBoundCfg (some .finish) [] [] [] o) := by
  simp [FinTM2.step,steinerOneBoundRangeMachine,oneBoundCfg,Turing.TM2.step,Turing.TM2.stepAux,
    oneBoundProgram,oneBoundObserve,oneBound_update1]
  rfl

private theorem oneBound_outputSymbol (symbol : SteinerRawRangeSymbol) (i o : List SteinerRawRangeSymbol) :
    steinerOneBoundRangeMachine.step (oneBoundCfg (some .finish) i [] [] (symbol::o)) =
      some (oneBoundCfg (some .finish) (symbol::i) [] [] o) := by
  simp [FinTM2.step,steinerOneBoundRangeMachine,oneBoundCfg,Turing.TM2.step,Turing.TM2.stepAux,
    oneBoundProgram,oneBoundObserve,oneBound_update0,oneBound_update3]
  rfl

private theorem oneBound_outputDone (i : List SteinerRawRangeSymbol) :
    steinerOneBoundRangeMachine.step (oneBoundCfg (some .finish) i [] [] []) =
      some (oneBoundCfg none i [] [] []) := by
  simp [FinTM2.step,steinerOneBoundRangeMachine,oneBoundCfg,Turing.TM2.step,Turing.TM2.stepAux,
    oneBoundProgram,oneBoundObserve,oneBound_update3]
  rfl

private def oneBoundOne {a b : steinerOneBoundRangeMachine.Cfg}
    (step : steinerOneBoundRangeMachine.step a = some b) :
    EvalsToInTime steinerOneBoundRangeMachine.step a (some b) 1 where
  steps := 1
  evals_in_steps := by change steinerOneBoundRangeMachine.step a = some b; exact step
  steps_le_m := le_rfl

private def oneBound_load (word : List Bool) (tail reversed : List SteinerRawRangeSymbol) :
    EvalsToInTime steinerOneBoundRangeMachine.step
      (oneBoundCfg (some .loadBound) (encodeSteinerSingleBoundWord word++tail) [] reversed [])
      (some (oneBoundCfg (some .restoreBound) tail [] ((oneBoundBits word).reverse++reversed) []))
      (word.length+1) := by
  induction word generalizing reversed with
  | nil => exact oneBoundOne (oneBound_loadDone tail reversed)
  | cons bit word ih =>
    have first := oneBoundOne (oneBound_loadBit bit (encodeSteinerSingleBoundWord word++tail) reversed)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (some (some bit)::reversed))
    simpa only [encodeSteinerSingleBoundWord,oneBoundBits,List.map_cons,List.cons_append,List.reverse_cons,
      List.append_assoc,List.singleton_append,List.nil_append,List.length_cons] using all

private def oneBound_restore (i b r o : List SteinerRawRangeSymbol) :
    EvalsToInTime steinerOneBoundRangeMachine.step (oneBoundCfg (some .restoreBound) i b r o)
      (some (oneBoundCfg (some .endpoint) i (r.reverse++b) [] o)) (r.length+1) := by
  induction r generalizing b with
  | nil => exact oneBoundOne (oneBound_restoreBoundDone i b o)
  | cons symbol reversed ih =>
    have first := oneBoundOne (oneBound_restoreBoundSymbol symbol i b reversed o)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (symbol::b))
    simpa only [List.reverse_cons,List.length_cons,List.append_assoc,List.singleton_append] using all

private def oneBound_endpointWord (word : List Bool) (tail bound out : List SteinerRawRangeSymbol) :
    EvalsToInTime steinerOneBoundRangeMachine.step
      (oneBoundCfg (some .endpoint) (encodeSteinerSingleBoundWord word++tail) bound [] out)
      (some (oneBoundCfg (some .copyBound) tail bound [] (some none::((oneBoundBits word).reverse++out))))
      (word.length+1) := by
  induction word generalizing out with
  | nil => exact oneBoundOne (oneBound_endpointDone tail bound out)
  | cons bit word ih =>
    have first := oneBoundOne (oneBound_endpointBit bit (encodeSteinerSingleBoundWord word++tail) bound out)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (some (some bit)::out))
    simpa only [encodeSteinerSingleBoundWord,oneBoundBits,List.map_cons,List.cons_append,List.reverse_cons,
      List.append_assoc,List.singleton_append,List.nil_append,List.length_cons] using all

private def oneBound_copy (input bound reversed out : List SteinerRawRangeSymbol) :
    EvalsToInTime steinerOneBoundRangeMachine.step (oneBoundCfg (some .copyBound) input bound reversed out)
      (some (oneBoundCfg (some .restoreBound) input [] (bound.reverse++reversed)
        (none::(bound.reverse++out)))) (bound.length+1) := by
  induction bound generalizing reversed out with
  | nil => exact oneBoundOne (oneBound_copyDone input reversed out)
  | cons symbol bound ih =>
    have first := oneBoundOne (oneBound_copySymbol symbol input bound reversed out)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (symbol::reversed) (symbol::out))
    simpa only [List.reverse_cons,List.length_cons,List.append_assoc,List.singleton_append] using all

private def oneBound_clear (bound out : List SteinerRawRangeSymbol) :
    EvalsToInTime steinerOneBoundRangeMachine.step (oneBoundCfg (some .clearBound) [] bound [] out)
      (some (oneBoundCfg (some .finish) [] [] [] out)) (bound.length+1) := by
  induction bound with
  | nil => exact oneBoundOne (oneBound_clearDone out)
  | cons symbol bound ih =>
    have first := oneBoundOne (oneBound_clearSymbol symbol bound out)
    exact EvalsToInTime.trans _ _ _ _ _ _ first ih

private def oneBound_finish (input out : List SteinerRawRangeSymbol) :
    EvalsToInTime steinerOneBoundRangeMachine.step (oneBoundCfg (some .finish) input [] [] out)
      (some (oneBoundCfg none (out.reverse++input) [] [] [])) (out.length+1) := by
  induction out generalizing input with
  | nil => exact oneBoundOne (oneBound_outputDone input)
  | cons symbol out ih =>
    have first := oneBoundOne (oneBound_outputSymbol symbol input out)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (symbol::input))
    simpa only [List.reverse_cons,List.length_cons,List.append_assoc,List.singleton_append] using all

private theorem oneBound_rawFrame (word bound : List Bool) :
    encodeSteinerRawRangeBatch [(word,bound)] =
      oneBoundBits word ++ (some none::oneBoundBits bound) ++ [none] := by
  simp [encodeSteinerRawRangeBatch,encodeSteinerBinaryComparison,oneBoundBits,List.map_map,Function.comp_def]

private def oneBound_eachEndpoint (bound : List Bool) (endpoints : List (List Bool)) (out : List SteinerRawRangeSymbol) :
    EvalsToInTime steinerOneBoundRangeMachine.step
      (oneBoundCfg (some .endpoint) (endpoints.flatMap encodeSteinerSingleBoundWord) (oneBoundBits bound) [] out)
      (some (oneBoundCfg (some .clearBound) [] (oneBoundBits bound) []
        ((encodeSteinerRawRangeBatch (expandSteinerSingleBound (bound,endpoints))).reverse++out)))
      (2*(encodeSteinerRawRangeBatch (expandSteinerSingleBound (bound,endpoints))).length+1) := by
  induction endpoints generalizing out with
  | nil => exact oneBoundOne (oneBound_endpointsDone (oneBoundBits bound) out)
  | cons word endpoints ih =>
    let tail := endpoints.flatMap encodeSteinerSingleBoundWord
    let bits := oneBoundBits bound
    let new := none::(bits.reverse ++ some none::((oneBoundBits word).reverse++out))
    have first := oneBound_endpointWord word tail bits out
    have copy := oneBound_copy tail bits [] (some none::((oneBoundBits word).reverse++out))
    rw [List.append_nil] at copy
    have restore := oneBound_restore tail [] bits.reverse new
    rw [List.reverse_reverse,List.append_nil,List.length_reverse] at restore
    have later := ih new
    have one := EvalsToInTime.trans _ _ _ _ _ _ first copy
    have recovered := EvalsToInTime.trans _ _ _ _ _ _ one restore
    have all := EvalsToInTime.trans _ _ _ _ _ _ recovered later
    let frames := encodeSteinerRawRangeBatch (expandSteinerSingleBound (bound,endpoints))
    have newest : new = (encodeSteinerRawRangeBatch [(word,bound)]).reverse++out := by
      rw [oneBound_rawFrame,List.reverse_append,List.reverse_append,List.reverse_cons]
      simp [new,bits,List.append_assoc]
    have frameAppend : encodeSteinerRawRangeBatch (expandSteinerSingleBound (bound,word::endpoints)) =
        encodeSteinerRawRangeBatch [(word,bound)]++frames := by
      simp [expandSteinerSingleBound,encodeSteinerRawRangeBatch,frames]
    have final : frames.reverse++new =
        (encodeSteinerRawRangeBatch (expandSteinerSingleBound (bound,word::endpoints))).reverse++out := by
      rw [newest,frameAppend,List.reverse_append,List.append_assoc]
    have paid : (2*frames.length+1)+((bits.length+1)+((bits.length+1)+(word.length+1))) ≤
        2*(encodeSteinerRawRangeBatch (expandSteinerSingleBound (bound,word::endpoints))).length+1 := by
      rw [frameAppend,oneBound_rawFrame]
      simp only [List.length_append,List.length_cons,List.length_nil,oneBoundBits,List.length_map,bits]
      omega
    have result := congrArg (fun answer => some (oneBoundCfg (some .clearBound) [] bits [] answer)) final
    exact ⟨⟨all.steps,all.evals_in_steps.trans result⟩,all.steps_le_m.trans paid⟩

private theorem oneBound_init (input : List SteinerRawRangeSymbol) :
    initList steinerOneBoundRangeMachine input = oneBoundCfg (some .loadBound) input [] [] [] := by
  unfold initList oneBoundCfg
  apply congrArg (fun stk : Fin 4 → List SteinerRawRangeSymbol =>
    (⟨some .loadBound,none,stk⟩ : steinerOneBoundRangeMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem oneBound_halt (out : List SteinerRawRangeSymbol) :
    haltList steinerOneBoundRangeMachine out = oneBoundCfg none out [] [] [] := by
  unfold haltList oneBoundCfg
  apply congrArg (fun stk : Fin 4 → List SteinerRawRangeSymbol =>
    (⟨none,none,stk⟩ : steinerOneBoundRangeMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- Expand every endpoint against the supplied bound. The bound tape
is restored after each copy and cleared before halting. -/
def steinerOneBoundRangeMachine_run (request : SteinerSingleBoundInput) :
    TM2OutputsInTime steinerOneBoundRangeMachine (encodeSteinerSingleBound request)
      (some (encodeSteinerRawRangeBatch (expandSteinerSingleBound request)))
      (3*(encodeSteinerRawRangeBatch (expandSteinerSingleBound request)).length+3*request.1.length+5) := by
  rcases request with ⟨bound,endpoints⟩
  let tail := endpoints.flatMap encodeSteinerSingleBoundWord
  let bits := oneBoundBits bound
  let out := encodeSteinerRawRangeBatch (expandSteinerSingleBound (bound,endpoints))
  have load := oneBound_load bound tail []
  rw [List.append_nil] at load
  have restore := oneBound_restore tail [] bits.reverse []
  rw [List.reverse_reverse,List.append_nil,List.length_reverse] at restore
  have endpointsRun := oneBound_eachEndpoint bound endpoints []
  rw [List.append_nil] at endpointsRun
  have clear := oneBound_clear bits out.reverse
  have finish := oneBound_finish [] out.reverse
  rw [List.reverse_reverse,List.append_nil,List.length_reverse] at finish
  have prepared := EvalsToInTime.trans _ _ _ _ _ _ load restore
  have expanded := EvalsToInTime.trans _ _ _ _ _ _ prepared endpointsRun
  have cleared := EvalsToInTime.trans _ _ _ _ _ _ expanded clear
  have all := EvalsToInTime.trans _ _ _ _ _ _ cleared finish
  change EvalsToInTime steinerOneBoundRangeMachine.step _ (some (haltList steinerOneBoundRangeMachine _)) _
  rw [oneBound_init,oneBound_halt]
  refine ⟨all.toEvalsTo,?_⟩
  have spent := all.steps_le_m
  change all.steps ≤ (out.length+1)+((bits.length+1)+((2*out.length+1)+((bits.length+1)+(bound.length+1)))) at spent
  simp only [bits,oneBoundBits,List.length_map] at spent
  change all.steps ≤ 3*out.length+3*bound.length+5
  omega

private theorem oneBound_endpointFrames_length (endpoints : List (List Bool)) :
    (endpoints.flatMap encodeSteinerSingleBoundWord).length =
      (endpoints.map List.length).sum+endpoints.length := by
  induction endpoints with
  | nil => rfl
  | cons word endpoints ih =>
    simp only [List.flatMap_cons,List.length_append,encodeSteinerSingleBoundWord,oneBoundBits,List.length_map,
      List.length_cons,List.length_nil,List.map_cons,List.sum_cons] at ih ⊢
    omega

/-- The output size is the endpoint bits plus one copied bound and two
dividers per endpoint. -/
theorem encodeSteinerSingleBound_expanded_length (bound : List Bool) (endpoints : List (List Bool)) :
    (encodeSteinerRawRangeBatch (expandSteinerSingleBound (bound,endpoints))).length =
      (endpoints.map List.length).sum+endpoints.length*(bound.length+2) := by
  induction endpoints with
  | nil => simp [expandSteinerSingleBound,encodeSteinerRawRangeBatch]
  | cons word endpoints ih =>
    have divided : encodeSteinerRawRangeBatch (expandSteinerSingleBound (bound,word::endpoints)) =
        encodeSteinerRawRangeBatch [(word,bound)]++
          encodeSteinerRawRangeBatch (expandSteinerSingleBound (bound,endpoints)) := by
      simp [encodeSteinerRawRangeBatch,expandSteinerSingleBound]
    rw [divided,List.length_append,oneBound_rawFrame,ih]
    simp only [List.length_append,List.length_cons,List.length_nil,oneBoundBits,List.length_map,
      List.map_cons,List.sum_cons,Nat.succ_mul]
    omega

/-- Supplying the bound once still gives a polynomial in the original
framed input size, including empty bounds and endpoint words. -/
noncomputable def steinerOneBoundRangeMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerSingleBound encodeSteinerRawRangeBatch expandSteinerSingleBound where
  tm := steinerOneBoundRangeMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 3*Polynomial.X^2+Polynomial.C 6*Polynomial.X+Polynomial.C 5
  outputsFun request := by
    rcases request with ⟨bound,endpoints⟩
    let x := (encodeSteinerSingleBound (bound,endpoints)).length
    let mass := (endpoints.map List.length).sum
    let output := (encodeSteinerRawRangeBatch (expandSteinerSingleBound (bound,endpoints))).length
    have inputEq : x = bound.length+1+(mass+endpoints.length) := by
      change (encodeSteinerSingleBoundWord bound ++ endpoints.flatMap encodeSteinerSingleBoundWord).length = _
      rw [List.length_append,oneBound_endpointFrames_length]
      simp [encodeSteinerSingleBoundWord,oneBoundBits,mass]
    have outputEq : output = mass+endpoints.length*(bound.length+2) :=
      encodeSteinerSingleBound_expanded_length bound endpoints
    have countFits : endpoints.length ≤ x := by omega
    have widthFits : bound.length+1 ≤ x := by omega
    have product := Nat.mul_le_mul countFits widthFits
    have decomposes : output = (mass+endpoints.length)+endpoints.length*(bound.length+1) := by
      rw [outputEq]
      ring
    have outputFits : output ≤ x+x^2 := by rw [pow_two]; omega
    have overhead : 3*output+3*bound.length+5 ≤ 3*x^2+6*x+5 := by omega
    have run := steinerOneBoundRangeMachine_run (bound,endpoints)
    change TM2OutputsInTime steinerOneBoundRangeMachine ((encodeSteinerSingleBound (bound,endpoints)).map id)
      (some ((encodeSteinerRawRangeBatch (expandSteinerSingleBound (bound,endpoints))).map id)) _
    simpa only [List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_C,x] using
      (show TM2OutputsInTime steinerOneBoundRangeMachine (encodeSteinerSingleBound (bound,endpoints))
        (some (encodeSteinerRawRangeBatch (expandSteinerSingleBound (bound,endpoints)))) (3*x^2+6*x+5) from
        ⟨run.toEvalsTo,run.steps_le_m.trans overhead⟩)

/-- Flatten graph rows before expanding the bound to obtain exactly the
range requests used by the guarded graph decoder. -/
theorem expandSteinerSingleBound_graph (bound : List Bool) (rows : List SteinerRangeWordPair) :
    expandSteinerSingleBound (bound,rows.flatMap fun row => [row.1,row.2]) =
      steinerRangeRequests bound rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [expandSteinerSingleBound,steinerRangeRequests,List.flatMap_cons,List.cons_append,List.nil_append,
      List.map_cons] at ih ⊢
    rw [ih]

end OnlineReachabilityPreservers
