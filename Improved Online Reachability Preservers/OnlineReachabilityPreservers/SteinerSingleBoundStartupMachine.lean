import OnlineReachabilityPreservers.SteinerOneBoundRangeMachine
import OnlineReachabilityPreservers.SteinerRawRangeSeedMachine

/-! Read one binary graph bound, check every endpoint, and sample the seed on acceptance. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev StartupSymbol := SteinerRawRangeSeedSymbol
private abbrev StartupExpandLabel := steinerOneBoundRangeMachine.Λ
private abbrev StartupFinishLabel := steinerRawRangeSeedMachine.Λ
private abbrev StartupExpandRegister := steinerOneBoundRangeMachine.σ
private abbrev StartupFinishRegister := steinerRawRangeSeedMachine.σ
private instance : Fintype StartupExpandLabel := steinerOneBoundRangeMachine.ΛFin
private instance : Fintype StartupFinishLabel := steinerRawRangeSeedMachine.ΛFin

private inductive StartupLabel where
  | collect
  | restore
  | expand (label : StartupExpandLabel)
  | finish (label : StartupFinishLabel)
  deriving Fintype

private abbrev StartupRegister := Option StartupSymbol × StartupExpandRegister × StartupFinishRegister
private abbrev StartupProgram := StackMachineTag.Program (Fin 5) StartupSymbol StartupLabel StartupRegister

private def singleStartupInitial : StartupRegister :=
  (none,steinerOneBoundRangeMachine.initialState,steinerRawRangeSeedMachine.initialState)

private def singleStartupObserve (_ : StartupRegister) (seen : Option StartupSymbol) : StartupRegister :=
  (seen,steinerOneBoundRangeMachine.initialState,steinerRawRangeSeedMachine.initialState)

private def singleStartupReadGraph : StartupSymbol → Option SteinerRawRangeSymbol
  | .inl symbol => some symbol
  | .inr _ => none

private def singleStartupExpandTag :
    StackMachineTag SteinerRawRangeSymbol StartupSymbol StartupExpandLabel StartupLabel
      StartupExpandRegister StartupRegister where
  writeSymbol := Sum.inl
  readSymbol := singleStartupReadGraph
  writeRegister r := (none,r,steinerRawRangeSeedMachine.initialState)
  readRegister r := r.2.1
  writeLabel := .expand
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def singleStartupFinishTag :
    StackMachineTag StartupSymbol StartupSymbol StartupFinishLabel StartupLabel
      StartupFinishRegister StartupRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (none,steinerOneBoundRangeMachine.initialState,r)
  readRegister r := r.2.2
  writeLabel := .finish
  read_written_symbol _ := rfl
  read_written_register _ := rfl

-- The encoder's input/output is already on the raw checker's input stack.
private def singleStartupSlots : Fin 4 ↪ Fin 5 where
  toFun := ![3,1,2,0]
  inj' := by
    intro i j equal
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction

private def singleStartupReady : StartupLabel :=
  .finish ((steinerRawRangeSeedPrepared [] []).l.getD steinerRawRangeSeedMachine.main)

private def singleStartupExpandInner :
    StartupLabel → StackMachineTag.Program (Fin 4) StartupSymbol StartupLabel StartupRegister
  | .expand l => singleStartupExpandTag.returningStatement singleStartupReady (steinerOneBoundRangeMachine.m l)
  | _ => halt

private def singleStartupProgram : StartupLabel → StartupProgram
  | .collect =>
    peek 4 singleStartupObserve <|
      branch (fun r => (r.1.bind singleStartupReadGraph).isSome)
        (pop 4 (fun r _ => r) <| push 0 (fun r => r.1.getD (Sum.inl none)) <|
          load (fun _ => singleStartupInitial) <| goto (fun _ => .collect))
        (load (fun _ => singleStartupInitial) <| goto (fun _ => .restore))
  | .restore =>
    pop 0 singleStartupObserve <|
      branch (fun r => r.1.isSome)
        (push 3 (fun r => r.1.getD (Sum.inl none)) <| load (fun _ => singleStartupInitial) <| goto (fun _ => .restore))
        (load (fun _ => singleStartupInitial) <| goto (fun _ => .expand steinerOneBoundRangeMachine.main))
  | .expand l => StackIndexEmbedding.statement singleStartupSlots (singleStartupExpandInner (.expand l))
  | .finish l => singleStartupFinishTag.statement (steinerRawRangeSeedMachine.m l)

/-- Read one supplied bound and the endpoints, then run the range checker
and finite sampler. The complete seed frame stays on the fifth stack. -/
abbrev steinerSingleBoundStartupMachine : FinTM2 where
  K := Fin 5
  k₀ := 4
  k₁ := 4
  Γ _ := StartupSymbol
  Λ := StartupLabel
  main := .collect
  σ := StartupRegister
  initialState := singleStartupInitial
  m := singleStartupProgram

private def singleStartupCfg (label : Option StartupLabel)
    (buffer graph input : List StartupSymbol) : steinerSingleBoundStartupMachine.Cfg where
  l := label
  var := singleStartupInitial
  stk := ![buffer,[],[],graph,input]

private theorem singleStartup_update0 (a b q next : List StartupSymbol) :
    Function.update (![a,[],[],b,q] : Fin 5 → List StartupSymbol) 0 next = ![next,[],[],b,q] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem singleStartup_update3 (a b q next : List StartupSymbol) :
    Function.update (![a,[],[],b,q] : Fin 5 → List StartupSymbol) 3 next = ![a,[],[],next,q] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem singleStartup_update4 (a b q next : List StartupSymbol) :
    Function.update (![a,[],[],b,q] : Fin 5 → List StartupSymbol) 4 next = ![a,[],[],b,next] := by
  funext i
  fin_cases i <;> simp [Function.update]

private def singleStartupOne {a b : steinerSingleBoundStartupMachine.Cfg}
    (step : steinerSingleBoundStartupMachine.step a = some b) :
    EvalsToInTime steinerSingleBoundStartupMachine.step a (some b) 1 where
  steps := 1
  evals_in_steps := by change steinerSingleBoundStartupMachine.step a = some b; exact step
  steps_le_m := le_rfl

private theorem singleStartup_collectSymbol (symbol : SteinerRawRangeSymbol) (buffer tail : List StartupSymbol) :
    steinerSingleBoundStartupMachine.step (singleStartupCfg (some .collect) buffer [] (Sum.inl symbol::tail)) =
      some (singleStartupCfg (some .collect) (Sum.inl symbol::buffer) [] tail) := by
  simp [FinTM2.step,steinerSingleBoundStartupMachine,singleStartupCfg,Turing.TM2.step,Turing.TM2.stepAux,
    singleStartupProgram,singleStartupObserve,singleStartupReadGraph,singleStartup_update0,singleStartup_update4]
  rfl

private theorem singleStartup_collectDone (buffer : List StartupSymbol) (seed : List (Option Bool)) :
    steinerSingleBoundStartupMachine.step (singleStartupCfg (some .collect) buffer [] (seed.map Sum.inr)) =
      some (singleStartupCfg (some .restore) buffer [] (seed.map Sum.inr)) := by
  cases seed <;>
    simp [FinTM2.step,steinerSingleBoundStartupMachine,singleStartupCfg,Turing.TM2.step,Turing.TM2.stepAux,
      singleStartupProgram,singleStartupObserve,singleStartupReadGraph] <;> rfl

private theorem singleStartup_restoreSymbol (symbol : StartupSymbol) (buffer graph input : List StartupSymbol) :
    steinerSingleBoundStartupMachine.step (singleStartupCfg (some .restore) (symbol::buffer) graph input) =
      some (singleStartupCfg (some .restore) buffer (symbol::graph) input) := by
  simp [FinTM2.step,steinerSingleBoundStartupMachine,singleStartupCfg,Turing.TM2.step,Turing.TM2.stepAux,
    singleStartupProgram,singleStartupObserve,singleStartup_update0,singleStartup_update3]
  rfl

private theorem singleStartup_restoreDone (graph input : List StartupSymbol) :
    steinerSingleBoundStartupMachine.step (singleStartupCfg (some .restore) [] graph input) =
      some (singleStartupCfg (some (.expand steinerOneBoundRangeMachine.main)) [] graph input) := by
  simp [FinTM2.step,steinerSingleBoundStartupMachine,singleStartupCfg,Turing.TM2.step,Turing.TM2.stepAux,
    singleStartupProgram,singleStartupObserve,singleStartup_update0]
  rfl

private def singleStartup_collect (graph : List SteinerRawRangeSymbol) (buffer : List StartupSymbol)
    (seed : List (Option Bool)) :
    EvalsToInTime steinerSingleBoundStartupMachine.step
      (singleStartupCfg (some .collect) buffer [] (graph.map Sum.inl ++ seed.map Sum.inr))
      (some (singleStartupCfg (some .restore) ((graph.map Sum.inl).reverse++buffer) [] (seed.map Sum.inr)))
      (graph.length+1) := by
  induction graph generalizing buffer with
  | nil => exact singleStartupOne (singleStartup_collectDone buffer seed)
  | cons symbol graph ih =>
    have first := singleStartupOne (singleStartup_collectSymbol symbol buffer (graph.map Sum.inl ++ seed.map Sum.inr))
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (Sum.inl symbol::buffer))
    simpa only [List.map_cons,List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,
      List.nil_append,List.length_cons] using all

private def singleStartup_restore (buffer graph input : List StartupSymbol) :
    EvalsToInTime steinerSingleBoundStartupMachine.step
      (singleStartupCfg (some .restore) buffer graph input)
      (some (singleStartupCfg (some (.expand steinerOneBoundRangeMachine.main)) [] (buffer.reverse++graph) input))
      (buffer.length+1) := by
  induction buffer generalizing graph with
  | nil => exact singleStartupOne (singleStartup_restoreDone graph input)
  | cons symbol buffer ih =>
    have first := singleStartupOne (singleStartup_restoreSymbol symbol buffer graph input)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (symbol::graph))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons] using all

private def singleStartupPassive (seed : List (Option Bool)) (i : Fin 5) : List StartupSymbol :=
  if i = 4 then seed.map Sum.inr else []

private theorem singleStartupSlots_excludes_input (i : Fin 4) : singleStartupSlots i ≠ 4 := by
  fin_cases i <;> decide

private noncomputable def singleStartupExpandCfg (seed : List (Option Bool)) (c : steinerOneBoundRangeMachine.Cfg) :
    steinerSingleBoundStartupMachine.Cfg :=
  StackIndexEmbedding.configuration singleStartupSlots (singleStartupPassive seed)
    (singleStartupExpandTag.returningConfiguration singleStartupReady c)

private theorem singleStartup_expandStep (seed : List (Option Bool)) {c after : steinerOneBoundRangeMachine.Cfg}
    (move : steinerOneBoundRangeMachine.step c = some after) :
    steinerSingleBoundStartupMachine.step (singleStartupExpandCfg seed c) =
      some (singleStartupExpandCfg seed after) := by
  have tagged := singleStartupExpandTag.step_embedded_return singleStartupReady (base := steinerOneBoundRangeMachine.m)
    (host := singleStartupExpandInner) (fun _ => rfl) move
  have framed := StackIndexEmbedding.step_on singleStartupSlots (base := singleStartupExpandInner)
    (singleStartupPassive seed) (singleStartupExpandTag.returningConfiguration singleStartupReady c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem singleStartup_expandTapes (seed : List (Option Bool)) (c : steinerOneBoundRangeMachine.Cfg)
    (word : List SteinerRawRangeSymbol) (tapes : c.stk = ![word,[],[],[]]) :
    (singleStartupExpandCfg seed c).stk = ![[],[],[],word.map Sum.inl,seed.map Sum.inr] := by
  have image (i : Fin 4) : (singleStartupExpandCfg seed c).stk (singleStartupSlots i) =
      ((![word,[],[],[]] : Fin 4 → List SteinerRawRangeSymbol) i).map Sum.inl := by
    change StackIndexEmbedding.tapesAt singleStartupSlots (fun i => (c.stk i).map Sum.inl) _
      (singleStartupSlots i) = _
    rw [StackIndexEmbedding.tapesAt_image,tapes]
  funext i
  fin_cases i
  · exact image 3
  · exact image 1
  · exact image 2
  · exact image 0
  · change StackIndexEmbedding.tapesAt singleStartupSlots _ (singleStartupPassive seed) 4 = _
    rw [StackIndexEmbedding.tapesAt_extra _ _ _ singleStartupSlots_excludes_input,singleStartupPassive,ite_eq_left rfl]
    rfl

private theorem singleStartup_expandInit (frame : List SteinerRawRangeSymbol) (seed : List (Option Bool)) :
    singleStartupExpandCfg seed (initList steinerOneBoundRangeMachine frame) =
      singleStartupCfg (some (.expand steinerOneBoundRangeMachine.main)) [] (frame.map Sum.inl) (seed.map Sum.inr) := by
  apply congrArg (fun stk : Fin 5 → List StartupSymbol =>
    (⟨some (.expand steinerOneBoundRangeMachine.main),singleStartupInitial,stk⟩ : steinerSingleBoundStartupMachine.Cfg))
  apply singleStartup_expandTapes
  funext i
  fin_cases i <;> rfl

private theorem singleStartup_expandReturn (frame : List SteinerRawRangeSymbol) (seed : List (Option Bool)) :
    singleStartupExpandCfg seed (haltList steinerOneBoundRangeMachine frame) =
      singleStartupFinishTag.configuration (steinerRawRangeSeedPrepared frame seed) := by
  have tapes := singleStartup_expandTapes seed (haltList steinerOneBoundRangeMachine frame) frame (by
    funext i
    fin_cases i <;> rfl)
  have target : (singleStartupFinishTag.configuration (steinerRawRangeSeedPrepared frame seed)).stk =
      ![[],[],[],frame.map Sum.inl,seed.map Sum.inr] := by
    funext i
    change ((steinerRawRangeSeedPrepared frame seed).stk i).map id = _
    rw [List.map_id_fun]
    rfl
  apply congrArg (fun stk : Fin 5 → List StartupSymbol =>
    (⟨some singleStartupReady,singleStartupInitial,stk⟩ : steinerSingleBoundStartupMachine.Cfg))
  exact tapes.trans target.symm

private def singleStartup_expand (request : SteinerSingleBoundInput) (seed : List (Option Bool)) :
    EvalsToInTime steinerSingleBoundStartupMachine.step
      (singleStartupCfg (some (.expand steinerOneBoundRangeMachine.main)) []
        ((encodeSteinerSingleBound request).map Sum.inl) (seed.map Sum.inr))
      (some (singleStartupFinishTag.configuration
        (steinerRawRangeSeedPrepared (encodeSteinerRawRangeBatch (expandSteinerSingleBound request)) seed)))
      (3*(encodeSteinerRawRangeBatch (expandSteinerSingleBound request)).length+3*request.1.length+5) := by
  let run := steinerOneBoundRangeMachine_run request
  refine ⟨⟨run.steps,?_⟩,run.steps_le_m⟩
  have expanded := iterate_map_some (singleStartupExpandCfg seed) (fun move => singleStartup_expandStep seed move)
    run.steps run.evals_in_steps
  change (flip bind steinerSingleBoundStartupMachine.step)^[run.steps]
      (some (singleStartupExpandCfg seed (initList steinerOneBoundRangeMachine (encodeSteinerSingleBound request)))) =
    some (singleStartupExpandCfg seed
      (haltList steinerOneBoundRangeMachine (encodeSteinerRawRangeBatch (expandSteinerSingleBound request)))) at expanded
  rw [singleStartup_expandInit,singleStartup_expandReturn] at expanded
  exact expanded

private theorem singleStartup_init (tape : List StartupSymbol) :
    initList steinerSingleBoundStartupMachine tape = singleStartupCfg (some .collect) [] [] tape := by
  apply congrArg (fun stk : Fin 5 → List StartupSymbol =>
    (⟨some .collect,singleStartupInitial,stk⟩ : steinerSingleBoundStartupMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem singleStartup_finishHalt (out : List StartupSymbol) :
    singleStartupFinishTag.configuration (haltList steinerRawRangeSeedMachine out) =
      haltList steinerSingleBoundStartupMachine out := by
  apply congrArg (fun stk : Fin 5 → List StartupSymbol =>
    (⟨none,singleStartupInitial,stk⟩ : steinerSingleBoundStartupMachine.Cfg))
  funext i
  change ((haltList steinerRawRangeSeedMachine out).stk i).map id =
    (haltList steinerSingleBoundStartupMachine out).stk i
  rw [List.map_id_fun]
  rfl

private def singleStartup_prepare (request : SteinerSingleBoundInput) (seed : List (Option Bool)) :
    EvalsToInTime steinerSingleBoundStartupMachine.step
      (initList steinerSingleBoundStartupMachine ((encodeSteinerSingleBound request).map Sum.inl ++ seed.map Sum.inr))
      (some (singleStartupFinishTag.configuration
        (steinerRawRangeSeedPrepared (encodeSteinerRawRangeBatch (expandSteinerSingleBound request)) seed)))
      (2*(encodeSteinerSingleBound request).length+
        3*(encodeSteinerRawRangeBatch (expandSteinerSingleBound request)).length+3*request.1.length+7) := by
  let frame := encodeSteinerSingleBound request
  have collected := singleStartup_collect frame [] seed
  rw [List.append_nil] at collected
  have restored := singleStartup_restore (frame.map Sum.inl).reverse [] (seed.map Sum.inr)
  rw [List.reverse_reverse,List.append_nil,List.length_reverse,List.length_map] at restored
  have ordered := EvalsToInTime.trans _ _ _ _ _ _ collected restored
  have prepared := EvalsToInTime.trans _ _ _ _ _ _ ordered (singleStartup_expand request seed)
  rw [singleStartup_init]
  exact ⟨prepared.toEvalsTo,by have spent := prepared.steps_le_m; dsimp only [frame] at spent; omega⟩

private def singleStartup_finish (request : SteinerSingleBoundInput) (seed : List (Option Bool)) (out : List StartupSymbol)
    {finishTime : ℕ}
    (finished : EvalsToInTime steinerRawRangeSeedMachine.step
      (steinerRawRangeSeedPrepared (encodeSteinerRawRangeBatch (expandSteinerSingleBound request)) seed)
      (some (haltList steinerRawRangeSeedMachine out)) finishTime) :
    TM2OutputsInTime steinerSingleBoundStartupMachine ((encodeSteinerSingleBound request).map Sum.inl ++ seed.map Sum.inr)
      (some out)
      (2*(encodeSteinerSingleBound request).length+
        3*(encodeSteinerRawRangeBatch (expandSteinerSingleBound request)).length+3*request.1.length+7+finishTime) := by
  let embedded := singleStartupFinishTag.evaluation (base := steinerRawRangeSeedMachine.m)
    (host := singleStartupProgram) (fun _ => rfl) finished
  have all := EvalsToInTime.trans _ _ _ _ _ _ (singleStartup_prepare request seed) embedded
  change EvalsToInTime steinerSingleBoundStartupMachine.step _ (some (haltList steinerSingleBoundStartupMachine out)) _
  rw [← singleStartup_finishHalt]
  exact ⟨all.toEvalsTo,by have spent := all.steps_le_m; omega⟩

abbrev SteinerSingleBoundStartupInput := SteinerSingleBoundInput × (ℕ × List Bool)

/-- The graph frame contains one bound and all endpoint words. The second
tag starts the seed request and supplies the unary count and seed bits. -/
def encodeSteinerSingleBoundStartup (request : SteinerSingleBoundStartupInput) : List SteinerRawRangeSeedSymbol :=
  (encodeSteinerSingleBound request.1).map Sum.inl ++ (encodeSteinerSeedTapeRequest request.2).map Sum.inr

def steinerSingleBoundStartupAnswer (request : SteinerSingleBoundStartupInput) : List SteinerRawRangeSeedSymbol :=
  steinerRawRangeSeedAnswer (expandSteinerSingleBound request.1,request.2)

/-- Run the single-bound graph check and sampler with exact output. On
rejection the original seed request remains behind the rejection marker. -/
def steinerSingleBoundStartupMachine_run (request : SteinerSingleBoundStartupInput) :
    TM2OutputsInTime steinerSingleBoundStartupMachine (encodeSteinerSingleBoundStartup request)
      (some (steinerSingleBoundStartupAnswer request))
      (2*(encodeSteinerSingleBound request.1).length+
        8*(encodeSteinerRawRangeBatch (expandSteinerSingleBound request.1)).length+
        3*request.1.1.length+3*request.2.1+12) := by
  have prepared := steinerRawRangeSeedMachine_finishPrepared (expandSteinerSingleBound request.1)
    (encodeSteinerSeedTapeRequest request.2) (splitSteinerSeedTapeOrReject request.2)
    (steinerSeedTapeMachine_runOrReject request.2)
  have run := singleStartup_finish request.1 (encodeSteinerSeedTapeRequest request.2) _ prepared
  exact ⟨run.toEvalsTo,by have spent := run.steps_le_m; omega⟩

/-- The polynomial is in the original single-bound encoding, including
the unary seed count and the full bit tape. -/
noncomputable def steinerSingleBoundStartupMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerSingleBoundStartup id steinerSingleBoundStartupAnswer where
  tm := steinerSingleBoundStartupMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 8*Polynomial.X^2+Polynomial.C 13*Polynomial.X+Polynomial.C 12
  outputsFun request := by
    let graph := request.1
    let xg := (encodeSteinerSingleBound graph).length
    let x := (encodeSteinerSingleBoundStartup request).length
    let y := (encodeSteinerRawRangeBatch (expandSteinerSingleBound graph)).length
    have inputEq : x = xg+request.2.1+request.2.2.length := by
      simp [x,xg,graph,encodeSteinerSingleBoundStartup,encodeSteinerSeedTapeRequest,Nat.add_assoc]
    have graphEq : xg = graph.1.length+1+((graph.2.map List.length).sum+graph.2.length) := by
      exact encodeSteinerSingleBound_length graph.1 graph.2
    have expands : y ≤ xg+xg^2 := encodeSteinerSingleBound_expanded_le graph
    have width : xg ≤ x := by omega
    have powers : xg^2 ≤ x^2 := by simpa only [pow_two] using Nat.mul_le_mul width width
    have fits : 2*xg+8*y+3*graph.1.length+3*request.2.1+12 ≤ 8*x^2+13*x+12 := by omega
    have run := steinerSingleBoundStartupMachine_run request
    change TM2OutputsInTime steinerSingleBoundStartupMachine ((encodeSteinerSingleBoundStartup request).map id)
      (some ((steinerSingleBoundStartupAnswer request).map id)) _
    simpa only [List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_C,x] using
      (show TM2OutputsInTime steinerSingleBoundStartupMachine (encodeSteinerSingleBoundStartup request)
        (some (steinerSingleBoundStartupAnswer request)) (8*x^2+13*x+12) from
        ⟨run.toEvalsTo,run.steps_le_m.trans fits⟩)

/-- With the supplied bound of value n, compare the graph endpoints at
allowance n plus their total bit count. On acceptance the machine
returns exactly the verified finite sampler result. -/
def steinerSingleBoundStartupMachine_guardedSampler {n size : ℕ} (bound : List Bool)
    (number : binaryWordValue bound = n) (rows : List SteinerRangeWordPair)
    (count : {b : ℕ // b = size}) (tape : List Bool) :
    let graph : SteinerSingleBoundInput := (bound,rows.flatMap fun row => [row.1,row.2])
    TM2OutputsInTime steinerSingleBoundStartupMachine (encodeSteinerSingleBoundStartup (graph,(size,tape)))
      (some (encodeSteinerRawRangeSeedAnswer
        ((decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1.isSome)
        (encodeSteinerSeedTapeRequest (size,tape))
        ((((readSteinerSeedWithWork count steinerBitTapeSource).run tape).map encodeSavedSteinerSeed).getD [])))
      (2*(encodeSteinerSingleBound graph).length+8*(binaryEndpointBits rows+2*rows.length*(bound.length+2))+
        3*bound.length+3*size+12) := by
  dsimp only
  let graph : SteinerSingleBoundInput := (bound,rows.flatMap fun row => [row.1,row.2])
  let seed := encodeSteinerSeedTapeRequest (size,tape)
  have requests : expandSteinerSingleBound graph = steinerRangeRequests bound rows :=
    expandSteinerSingleBound_graph bound rows
  have accepted : steinerRangeChecks (expandSteinerSingleBound graph) =
      ((decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1.isSome) := by
    rw [requests,steinerRangeRequests_guarded_flag bound number rows]
  have prepared := steinerRawRangeSeedMachine_finishPrepared (expandSteinerSingleBound graph) seed _
    (steinerSeedTapeMachine_refinesFiniteSampler count tape)
  have run := singleStartup_finish graph seed _ prepared
  rw [accepted,requests,encodeSteinerRawRangeRequests_length] at run
  exact ⟨run.toEvalsTo,by have spent := run.steps_le_m; dsimp only [graph] at spent; omega⟩

/-- A rejected graph leaves the complete seed frame unconsumed and gives a
transition bound independent of the unary count and random bits. -/
def steinerSingleBoundStartupMachine_rejectedGraph (request : SteinerSingleBoundStartupInput)
    (rejected : steinerRangeChecks (expandSteinerSingleBound request.1) = false) :
    TM2OutputsInTime steinerSingleBoundStartupMachine (encodeSteinerSingleBoundStartup request)
      (some (Sum.inl none::(encodeSteinerSeedTapeRequest request.2).map Sum.inr))
      (2*(encodeSteinerSingleBound request.1).length+
        8*(encodeSteinerRawRangeBatch (expandSteinerSingleBound request.1)).length+
        3*request.1.1.length+9) := by
  let seed := encodeSteinerSeedTapeRequest request.2
  have prepared := steinerRawRangeSeedMachine_finishRejected (expandSteinerSingleBound request.1) seed rejected
  have run := singleStartup_finish request.1 seed _ prepared
  exact ⟨run.toEvalsTo,by have spent := run.steps_le_m; omega⟩

end OnlineReachabilityPreservers
