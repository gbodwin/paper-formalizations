import OnlineReachabilityPreservers.SteinerGuardedUnaryGraphCountFrameMachine
import OnlineReachabilityPreservers.SteinerUnaryGraphArcCountMachine

/-! Compute the two finite graph cardinalities from one guarded binary frame. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev GraphDimsSymbol := SteinerRawRangeSeedSymbol
private abbrev GraphDimsFrameLabel := steinerGuardedUnaryGraphCountFrameMachine.Λ
private abbrev GraphDimsFrameRegister := steinerGuardedUnaryGraphCountFrameMachine.σ
private abbrev GraphDimsCountLabel := steinerUnaryGraphArcCountMachine.Λ
private abbrev GraphDimsCountRegister := steinerUnaryGraphArcCountMachine.σ
private instance : Fintype GraphDimsFrameLabel := steinerGuardedUnaryGraphCountFrameMachine.ΛFin
private instance : Fintype GraphDimsCountLabel := steinerUnaryGraphArcCountMachine.ΛFin

private inductive GraphDimsLabel where
  | frame (label : GraphDimsFrameLabel)
  | copy
  | restore
  | count (label : GraphDimsCountLabel)
  | delimit
  | prepend
  deriving Fintype

private abbrev GraphDimsRegister := Option GraphDimsSymbol × GraphDimsFrameRegister × GraphDimsCountRegister
private abbrev GraphDimsProgram := StackMachineTag.Program (Fin 9) GraphDimsSymbol GraphDimsLabel GraphDimsRegister

private def graphDimsInitial : GraphDimsRegister :=
  (none,steinerGuardedUnaryGraphCountFrameMachine.initialState,steinerUnaryGraphArcCountMachine.initialState)

private def graphDimsObserve (_ : GraphDimsRegister) (seen : Option GraphDimsSymbol) : GraphDimsRegister :=
  (seen,steinerGuardedUnaryGraphCountFrameMachine.initialState,steinerUnaryGraphArcCountMachine.initialState)

private def graphDimsNext (label : GraphDimsLabel) : GraphDimsProgram :=
  load (fun _ => graphDimsInitial) (goto (fun _ => label))

private def graphDimsFrameTag :
    StackMachineTag GraphDimsSymbol GraphDimsSymbol GraphDimsFrameLabel GraphDimsLabel
      GraphDimsFrameRegister GraphDimsRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (none,r,steinerUnaryGraphArcCountMachine.initialState)
  readRegister r := r.2.1
  writeLabel := .frame
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def graphDimsCountTag :
    StackMachineTag (Option Bool) GraphDimsSymbol GraphDimsCountLabel GraphDimsLabel
      GraphDimsCountRegister GraphDimsRegister where
  writeSymbol := Sum.inr
  readSymbol
    | .inl _ => none
    | .inr bit => some bit
  writeRegister r := (none,steinerGuardedUnaryGraphCountFrameMachine.initialState,r)
  readRegister r := r.2.2
  writeLabel := .count
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def graphDimsFrameSlots : Fin 8 ↪ Fin 9 :=
  ⟨Fin.castSucc,Fin.castSucc_injective 8⟩

/-- The unary counter reads stack 4 and writes stack 5 after swapping
the names of its two input/output stacks. -/
private def graphDimsCountSlots : Fin 8 ↪ Fin 9 :=
  ⟨fun i => ((Equiv.swap (4 : Fin 8) 5) i).castSucc,
    (Fin.castSucc_injective 8).comp (Equiv.swap (4 : Fin 8) 5).injective⟩

private def graphDimsFrameInner :
    GraphDimsLabel → StackMachineTag.Program (Fin 8) GraphDimsSymbol GraphDimsLabel GraphDimsRegister
  | .frame label =>
    graphDimsFrameTag.returningStatement .copy (steinerGuardedUnaryGraphCountFrameMachine.m label)
  | _ => halt

private def graphDimsCountInner :
    GraphDimsLabel → StackMachineTag.Program (Fin 8) GraphDimsSymbol GraphDimsLabel GraphDimsRegister
  | .count label => graphDimsCountTag.returningStatement .delimit (steinerUnaryGraphArcCountMachine.m label)
  | _ => halt

private def graphDimsIsRejected : Option GraphDimsSymbol → Bool
  | some (.inl _) => true
  | _ => false

private def graphDimsTally : GraphDimsSymbol := Sum.inr (some true)
private def graphDimsDivider : GraphDimsSymbol := Sum.inr none
private def graphDimsRejected : GraphDimsSymbol := Sum.inl none

private def graphDimsProgram : GraphDimsLabel → GraphDimsProgram
  | .frame label => StackIndexEmbedding.statement graphDimsFrameSlots (graphDimsFrameInner (.frame label))
  | .copy =>
    peek 4 graphDimsObserve <|
      branch (fun r => graphDimsIsRejected r.1)
        (pop 4 graphDimsObserve <|
          push 5 (fun _ => graphDimsRejected) (load (fun _ => graphDimsInitial) halt))
        (branch (fun r => r.1 == some graphDimsTally)
          (pop 4 graphDimsObserve <|
            push 0 (fun _ => graphDimsTally) <|
            push 8 (fun _ => graphDimsTally) (graphDimsNext .copy))
          (graphDimsNext .restore))
  | .restore =>
    pop 0 graphDimsObserve <|
      branch (fun r => r.1.isSome)
        (push 4 (fun _ => graphDimsTally) (graphDimsNext .restore))
        (graphDimsNext (.count steinerUnaryGraphArcCountMachine.main))
  | .count label => StackIndexEmbedding.statement graphDimsCountSlots (graphDimsCountInner (.count label))
  | .delimit => push 5 (fun _ => graphDimsDivider) (graphDimsNext .prepend)
  | .prepend =>
    pop 8 graphDimsObserve <|
      branch (fun r => r.1.isSome)
        (push 5 (fun _ => graphDimsTally) (graphDimsNext .prepend))
        (load (fun _ => graphDimsInitial) halt)

/-- Read a single-bound binary graph and return its vertex count and
distinct arc count in unary, or the failed-range marker. -/
abbrev steinerGuardedGraphDimensionsMachine : FinTM2 where
  K := Fin 9
  k₀ := 4
  k₁ := 5
  Γ _ := GraphDimsSymbol
  Λ := GraphDimsLabel
  main := .frame steinerGuardedUnaryGraphCountFrameMachine.main
  σ := GraphDimsRegister
  initialState := graphDimsInitial
  m := graphDimsProgram

private def graphDimsCfg (label : Option GraphDimsLabel) (buffer input out saved : List GraphDimsSymbol) :
    steinerGuardedGraphDimensionsMachine.Cfg where
  l := label
  var := graphDimsInitial
  stk := ![buffer,[],[],[],input,out,[],[],saved]

private theorem graphDims_update0 (a g f s w : List GraphDimsSymbol) :
    Function.update (![a,[],[],[],g,f,[],[],s] : Fin 9 → List GraphDimsSymbol) 0 w = ![w,[],[],[],g,f,[],[],s] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem graphDims_update4 (a g f s w : List GraphDimsSymbol) :
    Function.update (![a,[],[],[],g,f,[],[],s] : Fin 9 → List GraphDimsSymbol) 4 w = ![a,[],[],[],w,f,[],[],s] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem graphDims_update5 (a g f s w : List GraphDimsSymbol) :
    Function.update (![a,[],[],[],g,f,[],[],s] : Fin 9 → List GraphDimsSymbol) 5 w = ![a,[],[],[],g,w,[],[],s] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem graphDims_update8 (a g f s w : List GraphDimsSymbol) :
    Function.update (![a,[],[],[],g,f,[],[],s] : Fin 9 → List GraphDimsSymbol) 8 w = ![a,[],[],[],g,f,[],[],w] := by
  funext i
  fin_cases i <;> simp [Function.update]

private def graphDims_one {a b : steinerGuardedGraphDimensionsMachine.Cfg}
    (move : steinerGuardedGraphDimensionsMachine.step a = some b) :
    EvalsToInTime steinerGuardedGraphDimensionsMachine.step a (some b) 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := move

private noncomputable def graphDimsFrameTranslated (c : steinerGuardedUnaryGraphCountFrameMachine.Cfg) :
    steinerGuardedGraphDimensionsMachine.Cfg :=
  StackIndexEmbedding.configuration graphDimsFrameSlots (fun _ => [])
    (graphDimsFrameTag.returningConfiguration .copy c)

private theorem graphDims_frameStep {c after : steinerGuardedUnaryGraphCountFrameMachine.Cfg}
    (move : steinerGuardedUnaryGraphCountFrameMachine.step c = some after) :
    steinerGuardedGraphDimensionsMachine.step (graphDimsFrameTranslated c) = some (graphDimsFrameTranslated after) := by
  have tagged := graphDimsFrameTag.step_embedded_return .copy
    (base := steinerGuardedUnaryGraphCountFrameMachine.m) (host := graphDimsFrameInner) (fun _ => rfl) move
  have framed := StackIndexEmbedding.step_on graphDimsFrameSlots (base := graphDimsFrameInner)
    (fun _ => []) (graphDimsFrameTag.returningConfiguration .copy c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem graphDims_frameTapes (word : List GraphDimsSymbol) (c : steinerGuardedUnaryGraphCountFrameMachine.Cfg)
    (tapes : c.stk = ![[],[],[],[],word,[],[],[]]) :
    (graphDimsFrameTranslated c).stk = ![[],[],[],[],word,[],[],[],[]] := by
  have image (i : Fin 8) : (graphDimsFrameTranslated c).stk (graphDimsFrameSlots i) =
      (![[],[],[],[],word,[],[],[]] : Fin 8 → List GraphDimsSymbol) i := by
    change StackIndexEmbedding.tapesAt graphDimsFrameSlots (fun k => (c.stk k).map id) (fun _ => [])
      (graphDimsFrameSlots i) = _
    rw [StackIndexEmbedding.tapesAt_image,List.map_id,tapes]
  have extra : (graphDimsFrameTranslated c).stk 8 = [] := by
    change StackIndexEmbedding.tapesAt graphDimsFrameSlots (fun k => (c.stk k).map id) (fun _ => []) 8 = []
    exact StackIndexEmbedding.tapesAt_extra graphDimsFrameSlots _ _ (by intro i; fin_cases i <;> decide)
  funext i
  fin_cases i
  · exact image 0
  · exact image 1
  · exact image 2
  · exact image 3
  · exact image 4
  · exact image 5
  · exact image 6
  · exact image 7
  · exact extra

private theorem graphDims_frameInit (word : List GraphDimsSymbol) :
    graphDimsFrameTranslated (initList steinerGuardedUnaryGraphCountFrameMachine word) =
      initList steinerGuardedGraphDimensionsMachine word := by
  have lifted := graphDims_frameTapes word (initList steinerGuardedUnaryGraphCountFrameMachine word)
    (by funext i; fin_cases i <;> rfl)
  apply congrArg (fun stk : Fin 9 → List GraphDimsSymbol =>
    (⟨some (.frame steinerGuardedUnaryGraphCountFrameMachine.main),graphDimsInitial,stk⟩ :
      steinerGuardedGraphDimensionsMachine.Cfg))
  refine lifted.trans ?_
  funext i
  fin_cases i <;> rfl

private theorem graphDims_frameReturn (word : List GraphDimsSymbol) :
    graphDimsFrameTranslated (haltList steinerGuardedUnaryGraphCountFrameMachine word) =
      graphDimsCfg (some .copy) [] word [] [] := by
  apply congrArg (fun stk : Fin 9 → List GraphDimsSymbol =>
    (⟨some .copy,graphDimsInitial,stk⟩ : steinerGuardedGraphDimensionsMachine.Cfg))
  apply graphDims_frameTapes
  funext i
  fin_cases i <;> rfl

private def graphDims_frame {time : ℕ} (input out : List GraphDimsSymbol)
    (run : TM2OutputsInTime steinerGuardedUnaryGraphCountFrameMachine input (some out) time) :
    EvalsToInTime steinerGuardedGraphDimensionsMachine.step
      (initList steinerGuardedGraphDimensionsMachine input) (some (graphDimsCfg (some .copy) [] out [] [])) time := by
  refine ⟨⟨run.steps,?_⟩,run.steps_le_m⟩
  have moved := iterate_map_some graphDimsFrameTranslated (fun move => graphDims_frameStep move)
    run.steps run.evals_in_steps
  change (flip bind steinerGuardedGraphDimensionsMachine.step)^[run.steps]
    (some (graphDimsFrameTranslated (initList steinerGuardedUnaryGraphCountFrameMachine input))) =
    some (graphDimsFrameTranslated (haltList steinerGuardedUnaryGraphCountFrameMachine out)) at moved
  rwa [graphDims_frameInit,graphDims_frameReturn] at moved

private theorem graphDims_copyTally (buffer input saved : List GraphDimsSymbol) :
    steinerGuardedGraphDimensionsMachine.step (graphDimsCfg (some .copy) buffer (graphDimsTally::input) [] saved) =
      some (graphDimsCfg (some .copy) (graphDimsTally::buffer) input [] (graphDimsTally::saved)) := by
  simp [FinTM2.step,steinerGuardedGraphDimensionsMachine,graphDimsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    graphDimsProgram,graphDimsObserve,graphDimsNext,graphDimsIsRejected,graphDimsTally,
    graphDims_update0,graphDims_update4,graphDims_update8]
  rfl

private theorem graphDims_copyEnd (buffer input saved : List GraphDimsSymbol) :
    steinerGuardedGraphDimensionsMachine.step (graphDimsCfg (some .copy) buffer (graphDimsDivider::input) [] saved) =
      some (graphDimsCfg (some .restore) buffer (graphDimsDivider::input) [] saved) := by
  simp [FinTM2.step,steinerGuardedGraphDimensionsMachine,graphDimsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    graphDimsProgram,graphDimsObserve,graphDimsNext,graphDimsIsRejected,graphDimsDivider,graphDimsTally]
  rfl

private def graphDimsTallies (n : ℕ) : List GraphDimsSymbol := List.replicate n graphDimsTally

private theorem graphDimsTallies_separate (n : ℕ) (tail : List GraphDimsSymbol) :
    graphDimsTallies n++graphDimsTally::tail = graphDimsTallies (n+1)++tail := by
  simp only [graphDimsTallies,List.replicate_add,List.replicate_one,List.append_assoc,List.singleton_append]

private def graphDims_copy (n : ℕ) (buffer input saved : List GraphDimsSymbol) :
    EvalsToInTime steinerGuardedGraphDimensionsMachine.step
      (graphDimsCfg (some .copy) buffer (graphDimsTallies n++graphDimsDivider::input) [] saved)
      (some (graphDimsCfg (some .restore) (graphDimsTallies n++buffer) (graphDimsDivider::input) []
        (graphDimsTallies n++saved))) (n+1) := by
  induction n generalizing buffer saved with
  | zero => exact graphDims_one (graphDims_copyEnd buffer input saved)
  | succ n ih =>
    have first := graphDims_one (graphDims_copyTally buffer (graphDimsTallies n++graphDimsDivider::input) saved)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (graphDimsTally::buffer) (graphDimsTally::saved))
    rw [graphDimsTallies_separate,graphDimsTallies_separate] at all
    exact all

private theorem graphDims_restoreTally (buffer input saved : List GraphDimsSymbol) :
    steinerGuardedGraphDimensionsMachine.step (graphDimsCfg (some .restore) (graphDimsTally::buffer) input [] saved) =
      some (graphDimsCfg (some .restore) buffer (graphDimsTally::input) [] saved) := by
  simp [FinTM2.step,steinerGuardedGraphDimensionsMachine,graphDimsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    graphDimsProgram,graphDimsObserve,graphDimsNext,graphDims_update0,graphDims_update4]
  rfl

private theorem graphDims_restoreEnd (input saved : List GraphDimsSymbol) :
    steinerGuardedGraphDimensionsMachine.step (graphDimsCfg (some .restore) [] input [] saved) =
      some (graphDimsCfg (some (.count steinerUnaryGraphArcCountMachine.main)) [] input [] saved) := by
  simp [FinTM2.step,steinerGuardedGraphDimensionsMachine,graphDimsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    graphDimsProgram,graphDimsObserve,graphDimsNext,graphDims_update0]
  rfl

private def graphDims_restore (n : ℕ) (input saved : List GraphDimsSymbol) :
    EvalsToInTime steinerGuardedGraphDimensionsMachine.step
      (graphDimsCfg (some .restore) (graphDimsTallies n) input [] saved)
      (some (graphDimsCfg (some (.count steinerUnaryGraphArcCountMachine.main)) []
        (graphDimsTallies n++input) [] saved)) (n+1) := by
  induction n generalizing input with
  | zero => exact graphDims_one (graphDims_restoreEnd input saved)
  | succ n ih =>
    have first := graphDims_one (graphDims_restoreTally (graphDimsTallies n) input saved)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (graphDimsTally::input))
    rw [graphDimsTallies_separate] at all
    exact all

private def graphDimsCountPassive (saved : List GraphDimsSymbol) (i : Fin 9) : List GraphDimsSymbol :=
  if i = 8 then saved else []

private noncomputable def graphDimsCountTranslated (saved : List GraphDimsSymbol)
    (c : steinerUnaryGraphArcCountMachine.Cfg) : steinerGuardedGraphDimensionsMachine.Cfg :=
  StackIndexEmbedding.configuration graphDimsCountSlots (graphDimsCountPassive saved)
    (graphDimsCountTag.returningConfiguration .delimit c)

private theorem graphDims_countStep (saved : List GraphDimsSymbol) {c after : steinerUnaryGraphArcCountMachine.Cfg}
    (move : steinerUnaryGraphArcCountMachine.step c = some after) :
    steinerGuardedGraphDimensionsMachine.step (graphDimsCountTranslated saved c) =
      some (graphDimsCountTranslated saved after) := by
  have tagged := graphDimsCountTag.step_embedded_return .delimit
    (base := steinerUnaryGraphArcCountMachine.m) (host := graphDimsCountInner) (fun _ => rfl) move
  have framed := StackIndexEmbedding.step_on graphDimsCountSlots (base := graphDimsCountInner)
    (graphDimsCountPassive saved) (graphDimsCountTag.returningConfiguration .delimit c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem graphDims_countTapes (saved : List GraphDimsSymbol) (input out : List (Option Bool))
    (c : steinerUnaryGraphArcCountMachine.Cfg) (tapes : c.stk = ![[],[],[],[],out,input,[],[]]) :
    (graphDimsCountTranslated saved c).stk = ![[],[],[],[],input.map Sum.inr,out.map Sum.inr,[],[],saved] := by
  have image (i : Fin 8) : (graphDimsCountTranslated saved c).stk (graphDimsCountSlots i) =
      ((![[],[],[],[],out,input,[],[]] : Fin 8 → List (Option Bool)) i).map Sum.inr := by
    change StackIndexEmbedding.tapesAt graphDimsCountSlots (fun k => (c.stk k).map Sum.inr)
      (graphDimsCountPassive saved) (graphDimsCountSlots i) = _
    rw [StackIndexEmbedding.tapesAt_image,tapes]
  have extra : (graphDimsCountTranslated saved c).stk 8 = saved := by
    change StackIndexEmbedding.tapesAt graphDimsCountSlots (fun k => (c.stk k).map Sum.inr)
      (graphDimsCountPassive saved) 8 = _
    rw [StackIndexEmbedding.tapesAt_extra graphDimsCountSlots _ _ (by intro i; fin_cases i <;> decide)]
    rfl
  funext i
  fin_cases i
  · exact image 0
  · exact image 1
  · exact image 2
  · exact image 3
  · exact image 5
  · exact image 4
  · exact image 6
  · exact image 7
  · exact extra

private theorem graphDims_countInit (saved : List GraphDimsSymbol) (input : List (Option Bool)) :
    graphDimsCountTranslated saved (initList steinerUnaryGraphArcCountMachine input) =
      graphDimsCfg (some (.count steinerUnaryGraphArcCountMachine.main)) [] (input.map Sum.inr) [] saved := by
  apply congrArg (fun stk : Fin 9 → List GraphDimsSymbol =>
    (⟨some (.count steinerUnaryGraphArcCountMachine.main),graphDimsInitial,stk⟩ :
      steinerGuardedGraphDimensionsMachine.Cfg))
  apply graphDims_countTapes saved input [] (initList steinerUnaryGraphArcCountMachine input)
  funext i
  fin_cases i <;> rfl

private theorem graphDims_countReturn (saved : List GraphDimsSymbol) (out : List (Option Bool)) :
    graphDimsCountTranslated saved (haltList steinerUnaryGraphArcCountMachine out) =
      graphDimsCfg (some .delimit) [] [] (out.map Sum.inr) saved := by
  apply congrArg (fun stk : Fin 9 → List GraphDimsSymbol =>
    (⟨some .delimit,graphDimsInitial,stk⟩ : steinerGuardedGraphDimensionsMachine.Cfg))
  apply graphDims_countTapes saved [] out (haltList steinerUnaryGraphArcCountMachine out)
  funext i
  fin_cases i <;> rfl

private def graphDims_count {time : ℕ} (saved : List GraphDimsSymbol) (input out : List (Option Bool))
    (run : TM2OutputsInTime steinerUnaryGraphArcCountMachine input (some out) time) :
    EvalsToInTime steinerGuardedGraphDimensionsMachine.step
      (graphDimsCfg (some (.count steinerUnaryGraphArcCountMachine.main)) [] (input.map Sum.inr) [] saved)
      (some (graphDimsCfg (some .delimit) [] [] (out.map Sum.inr) saved)) time := by
  refine ⟨⟨run.steps,?_⟩,run.steps_le_m⟩
  have moved := iterate_map_some (graphDimsCountTranslated saved) (fun move => graphDims_countStep saved move)
    run.steps run.evals_in_steps
  change (flip bind steinerGuardedGraphDimensionsMachine.step)^[run.steps]
    (some (graphDimsCountTranslated saved (initList steinerUnaryGraphArcCountMachine input))) =
    some (graphDimsCountTranslated saved (haltList steinerUnaryGraphArcCountMachine out)) at moved
  rwa [graphDims_countInit,graphDims_countReturn] at moved

private theorem graphDims_delimitStep (out saved : List GraphDimsSymbol) :
    steinerGuardedGraphDimensionsMachine.step (graphDimsCfg (some .delimit) [] [] out saved) =
      some (graphDimsCfg (some .prepend) [] [] (graphDimsDivider::out) saved) := by
  simp [FinTM2.step,steinerGuardedGraphDimensionsMachine,graphDimsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    graphDimsProgram,graphDimsNext,graphDims_update5]
  rfl

private theorem graphDims_prependTally (out saved : List GraphDimsSymbol) :
    steinerGuardedGraphDimensionsMachine.step (graphDimsCfg (some .prepend) [] [] out (graphDimsTally::saved)) =
      some (graphDimsCfg (some .prepend) [] [] (graphDimsTally::out) saved) := by
  simp [FinTM2.step,steinerGuardedGraphDimensionsMachine,graphDimsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    graphDimsProgram,graphDimsObserve,graphDimsNext,graphDims_update5,graphDims_update8]
  rfl

private theorem graphDims_prependEnd (out : List GraphDimsSymbol) :
    steinerGuardedGraphDimensionsMachine.step (graphDimsCfg (some .prepend) [] [] out []) =
      some (graphDimsCfg none [] [] out []) := by
  simp [FinTM2.step,steinerGuardedGraphDimensionsMachine,graphDimsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    graphDimsProgram,graphDimsObserve,graphDims_update8]
  rfl

private def graphDims_prepend (n : ℕ) (out : List GraphDimsSymbol) :
    EvalsToInTime steinerGuardedGraphDimensionsMachine.step
      (graphDimsCfg (some .prepend) [] [] out (graphDimsTallies n))
      (some (graphDimsCfg none [] [] (graphDimsTallies n++out) [])) (n+1) := by
  induction n generalizing out with
  | zero => exact graphDims_one (graphDims_prependEnd out)
  | succ n ih =>
    have first := graphDims_one (graphDims_prependTally out (graphDimsTallies n))
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (graphDimsTally::out))
    rw [graphDimsTallies_separate] at all
    exact all

private theorem graphDims_rejectStep :
    steinerGuardedGraphDimensionsMachine.step (graphDimsCfg (some .copy) [] [graphDimsRejected] [] []) =
      some (graphDimsCfg none [] [] [graphDimsRejected] []) := by
  simp [FinTM2.step,steinerGuardedGraphDimensionsMachine,graphDimsCfg,Turing.TM2.step,Turing.TM2.stepAux,
    graphDimsProgram,graphDimsObserve,graphDimsIsRejected,graphDimsRejected,graphDims_update4,graphDims_update5]
  rfl

private theorem graphDims_halt (out : List GraphDimsSymbol) :
    haltList steinerGuardedGraphDimensionsMachine out = graphDimsCfg none [] [] out [] := by
  apply congrArg (fun stk : Fin 9 → List GraphDimsSymbol =>
    (⟨none,graphDimsInitial,stk⟩ : steinerGuardedGraphDimensionsMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- Right-tag the two unary counts and put one divider between them. -/
def encodeSteinerGraphDimensions (n m : ℕ) : List SteinerRawRangeSeedSymbol :=
  graphDimsTallies n++graphDimsDivider::graphDimsTallies m

private def graphDims_unaryCount {n : ℕ} (rows : List (Fin n × Fin n)) :
    let request : SteinerUnaryGraphQueryFrame := (n,rows.map steinerUnaryArcValues)
    let input := encodeSteinerUnaryGraphQueryFrame request
    let Y := input.length
    let C := Y^3+Y^2+Y
    EvalsToInTime steinerGuardedGraphDimensionsMachine.step
      (graphDimsCfg (some .copy) [] (input.map Sum.inr) [] [])
      (some (haltList steinerGuardedGraphDimensionsMachine (encodeSteinerGraphDimensions n rows.toFinset.card)))
      (5*C^2+16*C+2*Y^3+5*Y^2+9*Y+13+3*n+4) := by
  let request : SteinerUnaryGraphQueryFrame := (n,rows.map steinerUnaryArcValues)
  let input := encodeSteinerUnaryGraphQueryFrame request
  let graph := (encodeSteinerUnaryArcRows request.2).map (Sum.inr : Option Bool → GraphDimsSymbol)
  let Y := input.length
  let C := Y^3+Y^2+Y
  let m := rows.toFinset.card
  have framed : input.map Sum.inr = graphDimsTallies n++graphDimsDivider::graph := by
    simp only [input,encodeSteinerUnaryGraphQueryFrame,encodeSteinerUnaryArcEnumerationInput,request,graph,
      List.map_append,List.map_replicate,List.map_cons,graphDimsTallies,graphDimsTally,graphDimsDivider]
  have copied := graphDims_copy n [] graph []
  simp only [List.append_nil] at copied
  have restored := graphDims_restore n (graphDimsDivider::graph) (graphDimsTallies n)
  have ready := EvalsToInTime.trans _ _ _ _ _ _ copied restored
  rw [← framed] at ready
  have counted := graphDims_count (graphDimsTallies n) input (List.replicate m (some true))
    (steinerUnaryGraphArcCountMachine_finset rows)
  have out : (List.replicate m (some true)).map Sum.inr = graphDimsTallies m := by
    simp only [List.map_replicate,graphDimsTallies,graphDimsTally]
  rw [out] at counted
  have completed := EvalsToInTime.trans _ _ _ _ _ _ ready counted
  have split := EvalsToInTime.trans _ _ _ _ _ _ completed
    (graphDims_one (graphDims_delimitStep (graphDimsTallies m) (graphDimsTallies n)))
  have all := EvalsToInTime.trans _ _ _ _ _ _ split
    (graphDims_prepend n (graphDimsDivider::graphDimsTallies m))
  change EvalsToInTime steinerGuardedGraphDimensionsMachine.step _ (some (haltList _ _)) _
  rw [graphDims_halt]
  refine ⟨all.toEvalsTo,?_⟩
  have paid := all.steps_le_m
  change all.steps ≤ (n+1)+(1+((5*C^2+16*C+2*Y^3+5*Y^2+9*Y+13)+((n+1)+(n+1)))) at paid
  change all.steps ≤ 5*C^2+16*C+2*Y^3+5*Y^2+9*Y+13+3*n+4
  omega

private theorem graphDims_unaryLength {n : ℕ} (rows : List (Fin n × Fin n)) :
    (encodeSteinerUnaryGraphQueryFrame (n,rows.map steinerUnaryArcValues)).length ≤ (2*rows.length+1)*(n+1) := by
  have graph : (encodeSteinerUnaryArcRows (rows.map steinerUnaryArcValues)).length ≤ rows.length*(2*(n+1)) := by
    induction rows with
    | nil => simp [encodeSteinerUnaryArcRows,encodeSteinerUnaryEndpointValues]
    | cons row rows ih =>
      rw [List.map_cons,steinerUnaryArcValues,encodeSteinerUnaryArcRows_cons]
      simp only [List.length_append,List.length_replicate,List.length_cons]
      rw [Nat.succ_mul]
      have a := row.1.isLt
      have b := row.2.isLt
      omega
  rw [encodeSteinerUnaryGraphQueryFrame_length]
  change n+1+(encodeSteinerUnaryArcRows (rows.map steinerUnaryArcValues)).length ≤ _
  calc
    _ ≤ n+1+rows.length*(2*(n+1)) := Nat.add_le_add_left graph _
    _ = _ := by ring

/-- An accepted unary frame has at most (X(n+1)) symbols for raw
binary frame length (X) and decoded vertex count (n). -/
theorem encodeSteinerUnaryGraphQueryFrame_length_le_raw {n : ℕ} (bound : List Bool)
    (rows : List SteinerRangeWordPair) (decoded : List (Fin n × Fin n))
    (accepted : (decodeCheckedBinaryFinArcRowsWithWork (n+binaryEndpointBits rows) rows).1 = some decoded) :
    (encodeSteinerUnaryGraphQueryFrame (n,decoded.map steinerUnaryArcValues)).length ≤
      (encodeSteinerGuardedUnaryGraph bound rows).length*(n+1) := by
  have names := (decodeCheckedBinaryFinArcRowsWithWork_eq_some_iff _ rows decoded).mp accepted
  have count := congrArg List.length names.2
  simp only [List.length_map] at count
  apply (graphDims_unaryLength decoded).trans
  apply Nat.mul_le_mul_right
  rw [encodeSteinerGuardedUnaryGraph_length,count]
  omega

/-- A bound in the original binary input length and numeric vertex count. -/
def steinerGuardedGraphDimensionsTime (X n : ℕ) : ℕ :=
  let T := X*(n+1)
  let C := T^3+T^2+T
  8*X^2+28*X+10*X*n+9*n+5*C^2+16*C+2*T^3+5*T^2+9*T+48

private theorem graphDims_time_bound {X n Y : ℕ} (length : Y ≤ X*(n+1)) :
    let C := Y^3+Y^2+Y
    (5*C^2+16*C+2*Y^3+5*Y^2+9*Y+13+3*n+4)+(8*X^2+28*X+10*X*n+6*n+31) ≤
      steinerGuardedGraphDimensionsTime X n := by
  let T := X*(n+1)
  let C := Y^3+Y^2+Y
  let Cmax := T^3+T^2+T
  have cube : Y^3 ≤ T^3 := Nat.pow_le_pow_left length 3
  have square : Y^2 ≤ T^2 := Nat.pow_le_pow_left length 2
  have cap : C ≤ Cmax := by
    dsimp only [C,Cmax]
    omega
  have capSq : C^2 ≤ Cmax^2 := Nat.pow_le_pow_left cap 2
  change (5*C^2+16*C+2*Y^3+5*Y^2+9*Y+13+3*n+4)+(8*X^2+28*X+10*X*n+6*n+31) ≤
    8*X^2+28*X+10*X*n+9*n+5*Cmax^2+16*Cmax+2*T^3+5*T^2+9*T+48
  omega

/-- On accepted input the two dimensions are the exact vertex count and
the cardinality of the finite arc set represented by the decoded rows. -/
def steinerGuardedGraphDimensionsMachine_accepted {n : ℕ} (bound : List Bool) (number : binaryWordValue bound = n)
    (rows : List SteinerRangeWordPair) (decoded : List (Fin n × Fin n))
    (accepted : (decodeCheckedBinaryFinArcRowsWithWork (n+binaryEndpointBits rows) rows).1 = some decoded) :
    let X := (encodeSteinerGuardedUnaryGraph bound rows).length
    TM2OutputsInTime steinerGuardedGraphDimensionsMachine (encodeSteinerGuardedUnaryGraph bound rows)
      (some (encodeSteinerGraphDimensions n decoded.toFinset.card)) (steinerGuardedGraphDimensionsTime X n) := by
  have initial := graphDims_frame _ _
    (steinerGuardedUnaryGraphCountFrameMachine_accepted bound number rows decoded accepted)
  have all := EvalsToInTime.trans _ _ _ _ _ _ initial (graphDims_unaryCount decoded)
  refine ⟨all.toEvalsTo,all.steps_le_m.trans ?_⟩
  exact graphDims_time_bound (encodeSteinerUnaryGraphQueryFrame_length_le_raw bound rows decoded accepted)

/-- Rejection immediately forwards the single left-tagged marker. -/
def steinerGuardedGraphDimensionsMachine_rejected {n : ℕ} (bound : List Bool) (number : binaryWordValue bound = n)
    (rows : List SteinerRangeWordPair)
    (rejected : (decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1 = none) :
    let X := (encodeSteinerGuardedUnaryGraph bound rows).length
    TM2OutputsInTime steinerGuardedGraphDimensionsMachine (encodeSteinerGuardedUnaryGraph bound rows)
      (some [Sum.inl none]) (8*X^2+19*X+18) := by
  have initial := graphDims_frame _ _
    (steinerGuardedUnaryGraphCountFrameMachine_rejected bound number rows rejected)
  have all := EvalsToInTime.trans _ _ _ _ _ _ initial (graphDims_one graphDims_rejectStep)
  change EvalsToInTime steinerGuardedGraphDimensionsMachine.step _ (some (haltList _ _)) _
  rw [graphDims_halt]
  refine ⟨all.toEvalsTo,?_⟩
  have paid := all.steps_le_m
  omega

/-- The guarded graph has one pair of dimensions on acceptance. -/
def steinerGuardedGraphDimensionsAnswer (bound : List Bool) (rows : List SteinerRangeWordPair) :
    List SteinerRawRangeSeedSymbol :=
  let n := binaryWordValue bound
  match (decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1 with
  | none => [Sum.inl none]
  | some decoded => encodeSteinerGraphDimensions n decoded.toFinset.card

/-- The raw binary input suffices for the dimension computation. -/
def steinerGuardedGraphDimensionsMachine_run (bound : List Bool) (rows : List SteinerRangeWordPair) :
    let X := (encodeSteinerGuardedUnaryGraph bound rows).length
    let n := binaryWordValue bound
    TM2OutputsInTime steinerGuardedGraphDimensionsMachine (encodeSteinerGuardedUnaryGraph bound rows)
      (some (steinerGuardedGraphDimensionsAnswer bound rows)) (steinerGuardedGraphDimensionsTime X n) := by
  dsimp only
  unfold steinerGuardedGraphDimensionsAnswer
  dsimp only
  cases result : (decodeCheckedBinaryFinArcRowsWithWork (n := binaryWordValue bound)
      (binaryWordValue bound+binaryEndpointBits rows) rows).1 with
  | none =>
    let X := (encodeSteinerGuardedUnaryGraph bound rows).length
    let run := steinerGuardedGraphDimensionsMachine_rejected bound rfl rows result
    refine ⟨run.toEvalsTo,run.steps_le_m.trans ?_⟩
    change 8*X^2+19*X+18 ≤ steinerGuardedGraphDimensionsTime X (binaryWordValue bound)
    unfold steinerGuardedGraphDimensionsTime
    dsimp only
    omega
  | some decoded => exact steinerGuardedGraphDimensionsMachine_accepted bound rfl rows decoded result

end OnlineReachabilityPreservers
