import OnlineReachabilityPreservers.SteinerUnaryArcEnumerationMachine

/-! Build the arc table input from a unary vertex count and one graph frame. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev ArcFrameEnumLabel := steinerUnaryArcEnumerationMachine.Λ
private abbrev ArcFrameEnumRegister := steinerUnaryArcEnumerationMachine.σ
private instance : Fintype ArcFrameEnumLabel := steinerUnaryArcEnumerationMachine.ΛFin

private inductive ArcFrameLabel where
  | readBound
  | saveGraph
  | enumerate (label : ArcFrameEnumLabel)
  | separate
  | restoreGraph
  deriving Fintype

private abbrev ArcFrameRegister := Option (Option Bool) × ArcFrameEnumRegister
private abbrev ArcFrameProgram := StackMachineTag.Program (Fin 7) (Option Bool) ArcFrameLabel ArcFrameRegister

private def arcFrameInitial : ArcFrameRegister := (none,steinerUnaryArcEnumerationMachine.initialState)

private def arcFrameObserve (_ : ArcFrameRegister) (seen : Option (Option Bool)) : ArcFrameRegister :=
  (seen,steinerUnaryArcEnumerationMachine.initialState)

private def arcFrameNext (label : ArcFrameLabel) : ArcFrameProgram :=
  load (fun _ => arcFrameInitial) (goto (fun _ => label))

private def arcFrameTag :
    StackMachineTag (Option Bool) (Option Bool) ArcFrameEnumLabel ArcFrameLabel ArcFrameEnumRegister ArcFrameRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (none,r)
  readRegister := Prod.snd
  writeLabel := .enumerate
  read_written_symbol _ := rfl
  read_written_register _ := rfl

/-- The enumerator's input and output slot becomes the arc table slot. -/
private def arcFrameEnumSlots : Fin 5 ↪ Fin 7 :=
  ⟨fun i => (i+4).castSucc.castSucc,fun _ _ equal => add_right_cancel
    (Fin.castSucc_injective 5 (Fin.castSucc_injective 6 equal))⟩

private def arcFrameInner :
    ArcFrameLabel → StackMachineTag.Program (Fin 5) (Option Bool) ArcFrameLabel ArcFrameRegister
  | .enumerate label => arcFrameTag.returningStatement .separate (steinerUnaryArcEnumerationMachine.m label)
  | _ => halt

private def arcFrameProgram : ArcFrameLabel → ArcFrameProgram
  | .readBound =>
    pop 5 arcFrameObserve <|
      branch (fun r => r.1.join.isSome)
        (push 4 (fun _ => some true) (arcFrameNext .readBound))
        (arcFrameNext .saveGraph)
  | .saveGraph =>
    pop 5 arcFrameObserve <|
      branch (fun r => r.1.isSome)
        (push 6 (fun r => r.1.getD none) (arcFrameNext .saveGraph))
        (arcFrameNext (.enumerate steinerUnaryArcEnumerationMachine.main))
  | .enumerate label => StackIndexEmbedding.statement arcFrameEnumSlots (arcFrameInner (.enumerate label))
  | .separate => push 4 (fun _ => some false) (arcFrameNext .restoreGraph)
  | .restoreGraph =>
    pop 6 arcFrameObserve <|
      branch (fun r => r.1.isSome)
        (push 4 (fun r => r.1.getD none) (arcFrameNext .restoreGraph))
        (load (fun _ => arcFrameInitial) halt)

/-- Park the graph during enumeration, then put its original order and
one separator before the generated query frame. -/
abbrev steinerUnaryGraphQueryFrameMachine : FinTM2 where
  K := Fin 7
  k₀ := 5
  k₁ := 4
  Γ _ := Option Bool
  Λ := ArcFrameLabel
  main := .readBound
  σ := ArcFrameRegister
  initialState := arcFrameInitial
  m := arcFrameProgram

private def arcFrameCfg (label : Option ArcFrameLabel) (work input graph : List (Option Bool)) :
    steinerUnaryGraphQueryFrameMachine.Cfg where
  l := label
  var := arcFrameInitial
  stk := ![[],[],[],[],work,input,graph]

private theorem arcFrame_update4 (work input graph next : List (Option Bool)) :
    Function.update (![[],[],[],[],work,input,graph] : Fin 7 → List (Option Bool)) 4 next = ![[],[],[],[],next,input,graph] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem arcFrame_update5 (work input graph next : List (Option Bool)) :
    Function.update (![[],[],[],[],work,input,graph] : Fin 7 → List (Option Bool)) 5 next = ![[],[],[],[],work,next,graph] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem arcFrame_update6 (work input graph next : List (Option Bool)) :
    Function.update (![[],[],[],[],work,input,graph] : Fin 7 → List (Option Bool)) 6 next = ![[],[],[],[],work,input,next] := by
  funext i
  fin_cases i <;> simp [Function.update]

private def arcFrame_one {a b : steinerUnaryGraphQueryFrameMachine.Cfg}
    (step : steinerUnaryGraphQueryFrameMachine.step a = some b) :
    EvalsToInTime steinerUnaryGraphQueryFrameMachine.step a (some b) 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := step

private theorem arcFrame_boundSymbol (work input : List (Option Bool)) :
    steinerUnaryGraphQueryFrameMachine.step (arcFrameCfg (some .readBound) work (some true::input) []) =
      some (arcFrameCfg (some .readBound) (some true::work) input []) := by
  simp [FinTM2.step,steinerUnaryGraphQueryFrameMachine,arcFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcFrameProgram,arcFrameObserve,arcFrameNext,arcFrame_update4,arcFrame_update5]
  rfl

private theorem arcFrame_boundEnd (work input : List (Option Bool)) :
    steinerUnaryGraphQueryFrameMachine.step (arcFrameCfg (some .readBound) work (none::input) []) =
      some (arcFrameCfg (some .saveGraph) work input []) := by
  simp [FinTM2.step,steinerUnaryGraphQueryFrameMachine,arcFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcFrameProgram,arcFrameObserve,arcFrameNext,arcFrame_update5]
  rfl

private def arcFrame_bound (size : ℕ) (work input : List (Option Bool)) :
    EvalsToInTime steinerUnaryGraphQueryFrameMachine.step
      (arcFrameCfg (some .readBound) work (encodeSteinerUnaryArcEnumerationInput size++none::input) [])
      (some (arcFrameCfg (some .saveGraph) (encodeSteinerUnaryArcEnumerationInput size++work) input [])) (size+1) := by
  induction size generalizing work with
  | zero => exact arcFrame_one (arcFrame_boundEnd work input)
  | succ size ih =>
    have first := arcFrame_one (arcFrame_boundSymbol work (encodeSteinerUnaryArcEnumerationInput size++none::input))
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (some true::work))
    have order : encodeSteinerUnaryArcEnumerationInput size++some true::work =
        encodeSteinerUnaryArcEnumerationInput (size+1)++work := by
      simp only [encodeSteinerUnaryArcEnumerationInput,List.replicate_add,List.replicate_one,List.append_assoc,
        List.singleton_append]
    rw [order] at all
    exact all

private theorem arcFrame_saveSymbol (symbol : Option Bool) (work input graph : List (Option Bool)) :
    steinerUnaryGraphQueryFrameMachine.step (arcFrameCfg (some .saveGraph) work (symbol::input) graph) =
      some (arcFrameCfg (some .saveGraph) work input (symbol::graph)) := by
  simp [FinTM2.step,steinerUnaryGraphQueryFrameMachine,arcFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcFrameProgram,arcFrameObserve,arcFrameNext,arcFrame_update5,arcFrame_update6]
  rfl

private theorem arcFrame_saveEnd (work graph : List (Option Bool)) :
    steinerUnaryGraphQueryFrameMachine.step (arcFrameCfg (some .saveGraph) work [] graph) =
      some (arcFrameCfg (some (.enumerate steinerUnaryArcEnumerationMachine.main)) work [] graph) := by
  simp [FinTM2.step,steinerUnaryGraphQueryFrameMachine,arcFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcFrameProgram,arcFrameObserve,arcFrameNext,arcFrame_update5]
  rfl

private def arcFrame_save (work input graph : List (Option Bool)) :
    EvalsToInTime steinerUnaryGraphQueryFrameMachine.step
      (arcFrameCfg (some .saveGraph) work input graph)
      (some (arcFrameCfg (some (.enumerate steinerUnaryArcEnumerationMachine.main)) work [] (input.reverse++graph)))
      (input.length+1) := by
  induction input generalizing graph with
  | nil => exact arcFrame_one (arcFrame_saveEnd work graph)
  | cons symbol input ih =>
    have first := arcFrame_one (arcFrame_saveSymbol symbol work input graph)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (symbol::graph))
    simpa only [List.reverse_cons,List.length_cons,List.append_assoc,List.singleton_append] using all

private theorem arcFrame_split (work graph : List (Option Bool)) :
    steinerUnaryGraphQueryFrameMachine.step (arcFrameCfg (some .separate) work [] graph) =
      some (arcFrameCfg (some .restoreGraph) (some false::work) [] graph) := by
  simp [FinTM2.step,steinerUnaryGraphQueryFrameMachine,arcFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcFrameProgram,arcFrameNext,arcFrame_update4]
  rfl

private theorem arcFrame_restoreSymbol (symbol : Option Bool) (work graph : List (Option Bool)) :
    steinerUnaryGraphQueryFrameMachine.step (arcFrameCfg (some .restoreGraph) work [] (symbol::graph)) =
      some (arcFrameCfg (some .restoreGraph) (symbol::work) [] graph) := by
  simp [FinTM2.step,steinerUnaryGraphQueryFrameMachine,arcFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcFrameProgram,arcFrameObserve,arcFrameNext,arcFrame_update4,arcFrame_update6]
  rfl

private theorem arcFrame_restoreEnd (work : List (Option Bool)) :
    steinerUnaryGraphQueryFrameMachine.step (arcFrameCfg (some .restoreGraph) work [] []) =
      some (arcFrameCfg none work [] []) := by
  simp [FinTM2.step,steinerUnaryGraphQueryFrameMachine,arcFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcFrameProgram,arcFrameObserve,arcFrame_update6]
  rfl

private def arcFrame_restore (work graph : List (Option Bool)) :
    EvalsToInTime steinerUnaryGraphQueryFrameMachine.step
      (arcFrameCfg (some .restoreGraph) work [] graph)
      (some (arcFrameCfg none (graph.reverse++work) [] [])) (graph.length+1) := by
  induction graph generalizing work with
  | nil => exact arcFrame_one (arcFrame_restoreEnd work)
  | cons symbol graph ih =>
    have first := arcFrame_one (arcFrame_restoreSymbol symbol work graph)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (symbol::work))
    simpa only [List.reverse_cons,List.length_cons,List.append_assoc,List.singleton_append] using all

private def arcFramePassive (graph : List (Option Bool)) (i : Fin 7) : List (Option Bool) :=
  if i = 6 then graph else []

private noncomputable def arcFrameTranslated (graph : List (Option Bool)) (c : steinerUnaryArcEnumerationMachine.Cfg) :
    steinerUnaryGraphQueryFrameMachine.Cfg :=
  StackIndexEmbedding.configuration arcFrameEnumSlots (arcFramePassive graph)
    (arcFrameTag.returningConfiguration .separate c)

private theorem arcFrame_enumStep (graph : List (Option Bool)) {c after : steinerUnaryArcEnumerationMachine.Cfg}
    (move : steinerUnaryArcEnumerationMachine.step c = some after) :
    steinerUnaryGraphQueryFrameMachine.step (arcFrameTranslated graph c) = some (arcFrameTranslated graph after) := by
  have tagged := arcFrameTag.step_embedded_return .separate (base := steinerUnaryArcEnumerationMachine.m)
    (host := arcFrameInner) (fun _ => rfl) move
  have framed := StackIndexEmbedding.step_on arcFrameEnumSlots (base := arcFrameInner)
    (arcFramePassive graph) (arcFrameTag.returningConfiguration .separate c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem arcFrame_enumTapes (graph work : List (Option Bool)) (c : steinerUnaryArcEnumerationMachine.Cfg)
    (tapes : c.stk = ![work,[],[],[],[]]) :
    (arcFrameTranslated graph c).stk = ![[],[],[],[],work,[],graph] := by
  have image (i : Fin 5) : (arcFrameTranslated graph c).stk (arcFrameEnumSlots i) =
      (![work,[],[],[],[]] : Fin 5 → List (Option Bool)) i := by
    change StackIndexEmbedding.tapesAt arcFrameEnumSlots (fun k => (c.stk k).map id) _ (arcFrameEnumSlots i) = _
    rw [StackIndexEmbedding.tapesAt_image,List.map_id,tapes]
  have extra (i : Fin 7) (outside : ∀ j, arcFrameEnumSlots j ≠ i) :
      (arcFrameTranslated graph c).stk i = arcFramePassive graph i := by
    exact StackIndexEmbedding.tapesAt_extra arcFrameEnumSlots _ _ outside
  funext i
  fin_cases i
  · exact image 1
  · exact image 2
  · exact image 3
  · exact image 4
  · exact image 0
  · exact extra 5 (by intro j; fin_cases j <;> decide)
  · exact extra 6 (by intro j; fin_cases j <;> decide)

private theorem arcFrame_enumInit (graph work : List (Option Bool)) :
    arcFrameTranslated graph (initList steinerUnaryArcEnumerationMachine work) =
      arcFrameCfg (some (.enumerate steinerUnaryArcEnumerationMachine.main)) work [] graph := by
  apply congrArg (fun stk : Fin 7 → List (Option Bool) =>
    (⟨some (.enumerate steinerUnaryArcEnumerationMachine.main),arcFrameInitial,stk⟩ : steinerUnaryGraphQueryFrameMachine.Cfg))
  apply arcFrame_enumTapes
  funext i
  fin_cases i <;> rfl

private theorem arcFrame_enumReturn (graph work : List (Option Bool)) :
    arcFrameTranslated graph (haltList steinerUnaryArcEnumerationMachine work) =
      arcFrameCfg (some .separate) work [] graph := by
  apply congrArg (fun stk : Fin 7 → List (Option Bool) =>
    (⟨some .separate,arcFrameInitial,stk⟩ : steinerUnaryGraphQueryFrameMachine.Cfg))
  apply arcFrame_enumTapes
  funext i
  fin_cases i <;> rfl

private def arcFrame_enumerate (size : ℕ) (graph : List (Option Bool)) :
    EvalsToInTime steinerUnaryGraphQueryFrameMachine.step
      (arcFrameCfg (some (.enumerate steinerUnaryArcEnumerationMachine.main))
        (encodeSteinerUnaryArcEnumerationInput size) [] graph)
      (some (arcFrameCfg (some .separate) (steinerUnaryArcEnumerationAnswer size) [] graph)) (2*size^3+5*size^2+6*size+3) := by
  let run := steinerUnaryArcEnumerationMachine_run size
  refine ⟨⟨run.steps,?_⟩,run.steps_le_m⟩
  have executed := iterate_map_some (arcFrameTranslated graph) (fun move => arcFrame_enumStep graph move)
    run.steps run.evals_in_steps
  change (flip bind steinerUnaryGraphQueryFrameMachine.step)^[run.steps]
    (some (arcFrameTranslated graph (initList steinerUnaryArcEnumerationMachine (encodeSteinerUnaryArcEnumerationInput size)))) =
    some (arcFrameTranslated graph (haltList steinerUnaryArcEnumerationMachine (steinerUnaryArcEnumerationAnswer size))) at executed
  rwa [arcFrame_enumInit,arcFrame_enumReturn] at executed

abbrev SteinerUnaryGraphQueryFrame := ℕ × List (ℕ × ℕ)

/-- The initial unary vertex count is delimited from the graph rows. -/
def encodeSteinerUnaryGraphQueryFrame (request : SteinerUnaryGraphQueryFrame) : List (Option Bool) :=
  encodeSteinerUnaryArcEnumerationInput request.1++none::encodeSteinerUnaryArcRows request.2

/-- Generate the graph and all-pairs frame expected by the arc table. -/
def steinerUnaryGraphQueryFrameAnswer (request : SteinerUnaryGraphQueryFrame) : List (Option Bool) :=
  encodeSteinerUnaryArcTable (request.2,(steinerAllArcQueries request.1).map steinerUnaryArcValues)

private theorem arcFrame_init (word : List (Option Bool)) :
    initList steinerUnaryGraphQueryFrameMachine word = arcFrameCfg (some .readBound) [] word [] := by
  apply congrArg (fun stk : Fin 7 → List (Option Bool) =>
    (⟨some .readBound,arcFrameInitial,stk⟩ : steinerUnaryGraphQueryFrameMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem arcFrame_halt (word : List (Option Bool)) :
    haltList steinerUnaryGraphQueryFrameMachine word = arcFrameCfg none word [] [] := by
  apply congrArg (fun stk : Fin 7 → List (Option Bool) => (⟨none,arcFrameInitial,stk⟩ : steinerUnaryGraphQueryFrameMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- The machine uses the unary vertex count n and retains the original
ordered graph frame of length G while generating the exact query frame. -/
def steinerUnaryGraphQueryFrameMachine_run (request : SteinerUnaryGraphQueryFrame) :
    let n := request.1
    let G := (encodeSteinerUnaryArcRows request.2).length
    TM2OutputsInTime steinerUnaryGraphQueryFrameMachine (encodeSteinerUnaryGraphQueryFrame request)
      (some (steinerUnaryGraphQueryFrameAnswer request)) (2*n^3+5*n^2+7*n+2*G+7) := by
  rcases request with ⟨size,rows⟩
  let graph := encodeSteinerUnaryArcRows rows
  let queries := steinerUnaryArcEnumerationAnswer size
  have loaded := arcFrame_bound size [] graph
  rw [List.append_nil] at loaded
  have saved := arcFrame_save (encodeSteinerUnaryArcEnumerationInput size) graph []
  rw [List.append_nil] at saved
  have prepared := EvalsToInTime.trans _ _ _ _ _ _ loaded saved
  have listed := EvalsToInTime.trans _ _ _ _ _ _ prepared (arcFrame_enumerate size graph.reverse)
  have separated := EvalsToInTime.trans _ _ _ _ _ _ listed (arcFrame_one (arcFrame_split queries graph.reverse))
  have recovered := arcFrame_restore (some false::queries) graph.reverse
  rw [List.reverse_reverse,List.length_reverse] at recovered
  have all := EvalsToInTime.trans _ _ _ _ _ _ separated recovered
  change EvalsToInTime steinerUnaryGraphQueryFrameMachine.step _ (some (haltList steinerUnaryGraphQueryFrameMachine _)) _
  rw [arcFrame_init,arcFrame_halt]
  refine ⟨all.toEvalsTo,?_⟩
  have paid := all.steps_le_m
  dsimp only [graph] at paid
  dsimp only [Prod.fst,Prod.snd]
  omega

/-- Exact length of the initial unary count and graph frame. -/
theorem encodeSteinerUnaryGraphQueryFrame_length (request : SteinerUnaryGraphQueryFrame) :
    (encodeSteinerUnaryGraphQueryFrame request).length = request.1+1+(encodeSteinerUnaryArcRows request.2).length := by
  simp only [encodeSteinerUnaryGraphQueryFrame,encodeSteinerUnaryArcEnumerationInput,List.length_append,
    List.length_replicate,List.length_cons]
  omega

/-- The graph remains in the frame, followed by one separator and the
whole cubic-length candidate frame. -/
theorem steinerUnaryGraphQueryFrameAnswer_length (request : SteinerUnaryGraphQueryFrame) :
    (steinerUnaryGraphQueryFrameAnswer request).length = (encodeSteinerUnaryArcRows request.2).length+1+request.1^3+request.1^2 := by
  unfold steinerUnaryGraphQueryFrameAnswer encodeSteinerUnaryArcTable
  simp only [List.length_append,List.length_cons]
  change (encodeSteinerUnaryArcRows request.2).length+((steinerUnaryArcEnumerationAnswer request.1).length+1) = _
  rw [steinerUnaryArcEnumerationAnswer_length]
  omega

/-- The bound is cubic in the supplied unary graph frame length. -/
def steinerUnaryGraphQueryFrameMachine_cubic (request : SteinerUnaryGraphQueryFrame) :
    let X := (encodeSteinerUnaryGraphQueryFrame request).length
    TM2OutputsInTime steinerUnaryGraphQueryFrameMachine (encodeSteinerUnaryGraphQueryFrame request)
      (some (steinerUnaryGraphQueryFrameAnswer request)) (2*X^3+5*X^2+9*X+7) := by
  let X := (encodeSteinerUnaryGraphQueryFrame request).length
  have length : X = request.1+1+(encodeSteinerUnaryArcRows request.2).length := encodeSteinerUnaryGraphQueryFrame_length request
  have bounded : request.1 ≤ X := by omega
  have graphSize : (encodeSteinerUnaryArcRows request.2).length ≤ X := by omega
  have cube := Nat.pow_le_pow_left bounded 3
  have square := Nat.pow_le_pow_left bounded 2
  have run := steinerUnaryGraphQueryFrameMachine_run request
  refine ⟨run.toEvalsTo,run.steps_le_m.trans ?_⟩
  change _ ≤ 2*X^3+5*X^2+9*X+7
  omega

/-- Polynomial elapsed time from the supplied unary frame to the
prepared input of the arc count machine. -/
noncomputable def steinerUnaryGraphQueryFrameMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryGraphQueryFrame id steinerUnaryGraphQueryFrameAnswer where
  tm := steinerUnaryGraphQueryFrameMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2*Polynomial.X^3+Polynomial.C 5*Polynomial.X^2+Polynomial.C 9*Polynomial.X+Polynomial.C 7
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,
      Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_pow] using steinerUnaryGraphQueryFrameMachine_cubic request

end OnlineReachabilityPreservers
