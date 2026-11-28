import OnlineReachabilityPreservers.SteinerGuardedUnaryGraphMachine
import OnlineReachabilityPreservers.SteinerUnaryGraphQueryFrameMachine

/-! Keep the original vertex count and construct the guarded unary graph-count input. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev CountFrameSymbol := SteinerRawRangeSeedSymbol
private abbrev CountFrameGuardLabel := steinerGuardedUnaryGraphMachine.Λ
private abbrev CountFrameGuardRegister := steinerGuardedUnaryGraphMachine.σ
private abbrev CountFrameBoundLabel := steinerEndpointUnaryBatchMachine.Λ
private abbrev CountFrameBoundRegister := steinerEndpointUnaryBatchMachine.σ
private instance : Fintype CountFrameGuardLabel := steinerGuardedUnaryGraphMachine.ΛFin
private instance : Fintype CountFrameBoundLabel := steinerEndpointUnaryBatchMachine.ΛFin

private inductive CountFrameLabel where
  | save
  | restore
  | guard (label : CountFrameGuardLabel)
  | branchOnFlag
  | recover
  | bound (label : CountFrameBoundLabel)
  | delimit
  | prepend
  | discard
  deriving Fintype

private abbrev CountFrameRegister := Option CountFrameSymbol × CountFrameGuardRegister × CountFrameBoundRegister
private abbrev CountFrameProgram := StackMachineTag.Program (Fin 8) CountFrameSymbol CountFrameLabel CountFrameRegister

private def countFrameInitial : CountFrameRegister :=
  (none,steinerGuardedUnaryGraphMachine.initialState,steinerEndpointUnaryBatchMachine.initialState)

private def countFrameObserve (_ : CountFrameRegister) (seen : Option CountFrameSymbol) : CountFrameRegister :=
  (seen,steinerGuardedUnaryGraphMachine.initialState,steinerEndpointUnaryBatchMachine.initialState)

private def countFrameNext (label : CountFrameLabel) : CountFrameProgram :=
  load (fun _ => countFrameInitial) (goto (fun _ => label))

private def countFrameGuardTag :
    StackMachineTag CountFrameSymbol CountFrameSymbol CountFrameGuardLabel CountFrameLabel
      CountFrameGuardRegister CountFrameRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (none,r,steinerEndpointUnaryBatchMachine.initialState)
  readRegister r := r.2.1
  writeLabel := .guard
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def countFrameBoundTag :
    StackMachineTag (Option Bool) CountFrameSymbol CountFrameBoundLabel CountFrameLabel
      CountFrameBoundRegister CountFrameRegister where
  writeSymbol := Sum.inr
  readSymbol
    | .inl _ => none
    | .inr bit => some bit
  writeRegister r := (none,steinerGuardedUnaryGraphMachine.initialState,r)
  readRegister r := r.2.2
  writeLabel := .bound
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def countFrameGuardSlots : Fin 7 ↪ Fin 8 :=
  ⟨Fin.castSucc,Fin.castSucc_injective 7⟩

/-- Move the bound converter's shared input/output stack from 4 to 5,
leaving the graph on stack 4. -/
private def countFrameBoundSlots : Fin 6 ↪ Fin 8 :=
  ⟨fun i => ((4 : Fin 7).succAbove i).castSucc,
    (Fin.castSucc_injective 7).comp Fin.succAbove_right_injective⟩

private def countFrameGuardInner :
    CountFrameLabel → StackMachineTag.Program (Fin 7) CountFrameSymbol CountFrameLabel CountFrameRegister
  | .guard label =>
    countFrameGuardTag.returningStatement .branchOnFlag (steinerGuardedUnaryGraphMachine.m label)
  | _ => halt

private def countFrameBoundInner :
    CountFrameLabel → StackMachineTag.Program (Fin 6) CountFrameSymbol CountFrameLabel CountFrameRegister
  | .bound label => countFrameBoundTag.returningStatement .delimit (steinerEndpointUnaryBatchMachine.m label)
  | _ => halt

private def countFrameReadBit : Option CountFrameSymbol → Option Bool
  | some (.inl (some (some bit))) => some bit
  | _ => none

private def countFrameRejected : Option CountFrameSymbol → Bool
  | some (.inl _) => true
  | _ => false

private def countFrameProgram : CountFrameLabel → CountFrameProgram
  | .save =>
    peek 4 countFrameObserve <|
      branch (fun r => (countFrameReadBit r.1).isSome)
        (pop 4 countFrameObserve <|
          push 0 (fun r => r.1.getD (Sum.inl none)) <|
          push 7 (fun r => Sum.inr (countFrameReadBit r.1)) (countFrameNext .save))
        (countFrameNext .restore)
  | .restore =>
    pop 0 countFrameObserve <|
      branch (fun r => r.1.isSome)
        (push 4 (fun r => r.1.getD (Sum.inl none)) (countFrameNext .restore))
        (countFrameNext (.guard steinerGuardedUnaryGraphMachine.main))
  | .guard label =>
    StackIndexEmbedding.statement countFrameGuardSlots (countFrameGuardInner (.guard label))
  | .branchOnFlag =>
    peek 4 countFrameObserve <|
      branch (fun r => countFrameRejected r.1)
        (countFrameNext .discard)
        (push 5 (fun _ => Sum.inr none) (countFrameNext .recover))
  | .recover =>
    pop 7 countFrameObserve <|
      branch (fun r => r.1.isSome)
        (push 5 (fun r => r.1.getD (Sum.inr none)) (countFrameNext .recover))
        (countFrameNext (.bound steinerEndpointUnaryBatchMachine.main))
  | .bound label =>
    StackIndexEmbedding.statement countFrameBoundSlots (countFrameBoundInner (.bound label))
  | .delimit => push 4 (fun _ => Sum.inr none) (countFrameNext .prepend)
  | .prepend =>
    pop 5 countFrameObserve <|
      branch (fun r => r.1 == some (Sum.inr (some true)))
        (push 4 (fun _ => Sum.inr (some true)) (countFrameNext .prepend))
        (load (fun _ => countFrameInitial) halt)
  | .discard =>
    pop 7 countFrameObserve <|
      branch (fun r => r.1.isSome) (countFrameNext .discard) (load (fun _ => countFrameInitial) halt)

/-- Keep a copy of the original bound word through the guarded graph
decoder. Convert the bound to unary on acceptance, and discard it on
rejection. Successful frames are tagged for the unary arc count. -/
abbrev steinerGuardedUnaryGraphCountFrameMachine : FinTM2 where
  K := Fin 8
  k₀ := 4
  k₁ := 4
  Γ _ := CountFrameSymbol
  Λ := CountFrameLabel
  main := .save
  σ := CountFrameRegister
  initialState := countFrameInitial
  m := countFrameProgram

private def countFrameCfg (label : Option CountFrameLabel) (buffer graph bound saved : List CountFrameSymbol) :
    steinerGuardedUnaryGraphCountFrameMachine.Cfg where
  l := label
  var := countFrameInitial
  stk := ![buffer,[],[],[],graph,bound,[],saved]

private theorem countFrame_update0 (a g b s w : List CountFrameSymbol) :
    Function.update (![a,[],[],[],g,b,[],s] : Fin 8 → List CountFrameSymbol) 0 w = ![w,[],[],[],g,b,[],s] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem countFrame_update4 (a g b s w : List CountFrameSymbol) :
    Function.update (![a,[],[],[],g,b,[],s] : Fin 8 → List CountFrameSymbol) 4 w = ![a,[],[],[],w,b,[],s] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem countFrame_update5 (a g b s w : List CountFrameSymbol) :
    Function.update (![a,[],[],[],g,b,[],s] : Fin 8 → List CountFrameSymbol) 5 w = ![a,[],[],[],g,w,[],s] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem countFrame_update7 (a g b s w : List CountFrameSymbol) :
    Function.update (![a,[],[],[],g,b,[],s] : Fin 8 → List CountFrameSymbol) 7 w = ![a,[],[],[],g,b,[],w] := by
  funext i
  fin_cases i <;> simp [Function.update]

private def countFrame_one {a b : steinerGuardedUnaryGraphCountFrameMachine.Cfg}
    (move : steinerGuardedUnaryGraphCountFrameMachine.step a = some b) :
    EvalsToInTime steinerGuardedUnaryGraphCountFrameMachine.step a (some b) 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := move

private def countFrameRawBits (bound : List Bool) : List CountFrameSymbol :=
  bound.map fun b => Sum.inl (some (some b))

private def countFrameUnaryBits (bound : List Bool) : List CountFrameSymbol :=
  bound.map fun b => Sum.inr (some b)

private theorem countFrame_saveBit (bit : Bool) (buffer graph saved : List CountFrameSymbol) :
    steinerGuardedUnaryGraphCountFrameMachine.step
      (countFrameCfg (some .save) buffer (Sum.inl (some (some bit))::graph) [] saved) =
      some (countFrameCfg (some .save) (Sum.inl (some (some bit))::buffer) graph [] (Sum.inr (some bit)::saved)) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphCountFrameMachine,countFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    countFrameProgram,countFrameObserve,countFrameNext,countFrameReadBit,countFrame_update0,countFrame_update4,countFrame_update7]
  rfl

private theorem countFrame_saveEnd (buffer graph saved : List CountFrameSymbol) :
    steinerGuardedUnaryGraphCountFrameMachine.step
      (countFrameCfg (some .save) buffer (Sum.inl (some none)::graph) [] saved) =
      some (countFrameCfg (some .restore) buffer (Sum.inl (some none)::graph) [] saved) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphCountFrameMachine,countFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    countFrameProgram,countFrameObserve,countFrameNext,countFrameReadBit]
  rfl

private def countFrame_save (bound : List Bool) (buffer graph saved : List CountFrameSymbol) :
    EvalsToInTime steinerGuardedUnaryGraphCountFrameMachine.step
      (countFrameCfg (some .save) buffer (countFrameRawBits bound++Sum.inl (some none)::graph) [] saved)
      (some (countFrameCfg (some .restore) ((countFrameRawBits bound).reverse++buffer)
        (Sum.inl (some none)::graph) [] ((countFrameUnaryBits bound).reverse++saved))) (bound.length+1) := by
  induction bound generalizing buffer saved with
  | nil => exact countFrame_one (countFrame_saveEnd buffer graph saved)
  | cons bit bound ih =>
    have first := countFrame_one (countFrame_saveBit bit buffer (countFrameRawBits bound++Sum.inl (some none)::graph) saved)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first
      (ih (Sum.inl (some (some bit))::buffer) (Sum.inr (some bit)::saved))
    simpa only [countFrameRawBits,countFrameUnaryBits,List.map_cons,List.cons_append,List.reverse_cons,
      List.length_cons,List.append_assoc,List.singleton_append,List.nil_append] using all

private theorem countFrame_restoreBit (symbol : CountFrameSymbol) (buffer graph saved : List CountFrameSymbol) :
    steinerGuardedUnaryGraphCountFrameMachine.step
      (countFrameCfg (some .restore) (symbol::buffer) graph [] saved) =
      some (countFrameCfg (some .restore) buffer (symbol::graph) [] saved) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphCountFrameMachine,countFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    countFrameProgram,countFrameObserve,countFrameNext,countFrame_update0,countFrame_update4]
  rfl

private theorem countFrame_restoreEnd (graph saved : List CountFrameSymbol) :
    steinerGuardedUnaryGraphCountFrameMachine.step (countFrameCfg (some .restore) [] graph [] saved) =
      some (countFrameCfg (some (.guard steinerGuardedUnaryGraphMachine.main)) [] graph [] saved) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphCountFrameMachine,countFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    countFrameProgram,countFrameObserve,countFrameNext,countFrame_update0]
  rfl

private def countFrame_restore (buffer graph saved : List CountFrameSymbol) :
    EvalsToInTime steinerGuardedUnaryGraphCountFrameMachine.step (countFrameCfg (some .restore) buffer graph [] saved)
      (some (countFrameCfg (some (.guard steinerGuardedUnaryGraphMachine.main)) [] (buffer.reverse++graph) [] saved))
      (buffer.length+1) := by
  induction buffer generalizing graph with
  | nil => exact countFrame_one (countFrame_restoreEnd graph saved)
  | cons symbol buffer ih =>
    have first := countFrame_one (countFrame_restoreBit symbol buffer graph saved)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (symbol::graph))
    simpa only [List.reverse_cons,List.length_cons,List.append_assoc,List.singleton_append] using all

private def countFrameGuardPassive (saved : List CountFrameSymbol) (i : Fin 8) : List CountFrameSymbol :=
  if i = 7 then saved else []

private noncomputable def countFrameGuardTranslated (saved : List CountFrameSymbol)
    (c : steinerGuardedUnaryGraphMachine.Cfg) : steinerGuardedUnaryGraphCountFrameMachine.Cfg :=
  StackIndexEmbedding.configuration countFrameGuardSlots (countFrameGuardPassive saved)
    (countFrameGuardTag.returningConfiguration .branchOnFlag c)

private theorem countFrame_guardStep (saved : List CountFrameSymbol) {c after : steinerGuardedUnaryGraphMachine.Cfg}
    (move : steinerGuardedUnaryGraphMachine.step c = some after) :
    steinerGuardedUnaryGraphCountFrameMachine.step (countFrameGuardTranslated saved c) =
      some (countFrameGuardTranslated saved after) := by
  have tagged := countFrameGuardTag.step_embedded_return .branchOnFlag
    (base := steinerGuardedUnaryGraphMachine.m) (host := countFrameGuardInner) (fun _ => rfl) move
  have framed := StackIndexEmbedding.step_on countFrameGuardSlots (base := countFrameGuardInner)
    (countFrameGuardPassive saved) (countFrameGuardTag.returningConfiguration .branchOnFlag c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem countFrame_guardTapes (saved graph : List CountFrameSymbol) (c : steinerGuardedUnaryGraphMachine.Cfg)
    (tapes : c.stk = ![[],[],[],[],graph,[],[]]) :
    (countFrameGuardTranslated saved c).stk = ![[],[],[],[],graph,[],[],saved] := by
  have image (i : Fin 7) : (countFrameGuardTranslated saved c).stk (countFrameGuardSlots i) =
      (![[],[],[],[],graph,[],[]] : Fin 7 → List CountFrameSymbol) i := by
    change StackIndexEmbedding.tapesAt countFrameGuardSlots (fun k => (c.stk k).map id)
      (countFrameGuardPassive saved) (countFrameGuardSlots i) = _
    rw [StackIndexEmbedding.tapesAt_image,List.map_id,tapes]
  have extra : (countFrameGuardTranslated saved c).stk 7 = saved := by
    change StackIndexEmbedding.tapesAt countFrameGuardSlots (fun k => (c.stk k).map id) (countFrameGuardPassive saved) 7 = _
    rw [StackIndexEmbedding.tapesAt_extra countFrameGuardSlots _ _ (by intro j; fin_cases j <;> decide)]
    rfl
  funext i
  fin_cases i
  · exact image 0
  · exact image 1
  · exact image 2
  · exact image 3
  · exact image 4
  · exact image 5
  · exact image 6
  · exact extra

private theorem countFrame_guardInit (graph saved : List CountFrameSymbol) :
    countFrameGuardTranslated saved (initList steinerGuardedUnaryGraphMachine graph) =
      countFrameCfg (some (.guard steinerGuardedUnaryGraphMachine.main)) [] graph [] saved := by
  apply congrArg (fun stk : Fin 8 → List CountFrameSymbol =>
    (⟨some (.guard steinerGuardedUnaryGraphMachine.main),countFrameInitial,stk⟩ :
      steinerGuardedUnaryGraphCountFrameMachine.Cfg))
  apply countFrame_guardTapes
  funext i
  fin_cases i <;> rfl

private theorem countFrame_guardReturn (graph saved : List CountFrameSymbol) :
    countFrameGuardTranslated saved (haltList steinerGuardedUnaryGraphMachine graph) =
      countFrameCfg (some .branchOnFlag) [] graph [] saved := by
  apply congrArg (fun stk : Fin 8 → List CountFrameSymbol =>
    (⟨some .branchOnFlag,countFrameInitial,stk⟩ : steinerGuardedUnaryGraphCountFrameMachine.Cfg))
  apply countFrame_guardTapes
  funext i
  fin_cases i <;> rfl

private def countFrame_guard {time : ℕ} (input out saved : List CountFrameSymbol)
    (run : TM2OutputsInTime steinerGuardedUnaryGraphMachine input (some out) time) :
    EvalsToInTime steinerGuardedUnaryGraphCountFrameMachine.step
      (countFrameCfg (some (.guard steinerGuardedUnaryGraphMachine.main)) [] input [] saved)
      (some (countFrameCfg (some .branchOnFlag) [] out [] saved)) time := by
  refine ⟨⟨run.steps,?_⟩,run.steps_le_m⟩
  have moved := iterate_map_some (countFrameGuardTranslated saved) (fun move => countFrame_guardStep saved move)
    run.steps run.evals_in_steps
  change (flip bind steinerGuardedUnaryGraphCountFrameMachine.step)^[run.steps]
    (some (countFrameGuardTranslated saved (initList steinerGuardedUnaryGraphMachine input))) =
    some (countFrameGuardTranslated saved (haltList steinerGuardedUnaryGraphMachine out)) at moved
  rwa [countFrame_guardInit,countFrame_guardReturn] at moved

private theorem countFrame_acceptStep (graph : List (Option Bool)) (saved : List CountFrameSymbol) :
    steinerGuardedUnaryGraphCountFrameMachine.step
      (countFrameCfg (some .branchOnFlag) [] (graph.map Sum.inr) [] saved) =
      some (countFrameCfg (some .recover) [] (graph.map Sum.inr) [Sum.inr none] saved) := by
  cases graph <;>
    simp [FinTM2.step,steinerGuardedUnaryGraphCountFrameMachine,countFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
      countFrameProgram,countFrameObserve,countFrameNext,countFrameRejected,countFrame_update5] <;> rfl

private theorem countFrame_recoverSymbol (symbol : CountFrameSymbol) (graph bound saved : List CountFrameSymbol) :
    steinerGuardedUnaryGraphCountFrameMachine.step
      (countFrameCfg (some .recover) [] graph bound (symbol::saved)) =
      some (countFrameCfg (some .recover) [] graph (symbol::bound) saved) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphCountFrameMachine,countFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    countFrameProgram,countFrameObserve,countFrameNext,countFrame_update5,countFrame_update7]
  rfl

private theorem countFrame_recoverEnd (graph bound : List CountFrameSymbol) :
    steinerGuardedUnaryGraphCountFrameMachine.step (countFrameCfg (some .recover) [] graph bound []) =
      some (countFrameCfg (some (.bound steinerEndpointUnaryBatchMachine.main)) [] graph bound []) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphCountFrameMachine,countFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    countFrameProgram,countFrameObserve,countFrameNext,countFrame_update7]
  rfl

private def countFrame_recover (graph bound saved : List CountFrameSymbol) :
    EvalsToInTime steinerGuardedUnaryGraphCountFrameMachine.step (countFrameCfg (some .recover) [] graph bound saved)
      (some (countFrameCfg (some (.bound steinerEndpointUnaryBatchMachine.main)) [] graph (saved.reverse++bound) []))
      (saved.length+1) := by
  induction saved generalizing bound with
  | nil => exact countFrame_one (countFrame_recoverEnd graph bound)
  | cons symbol saved ih =>
    have first := countFrame_one (countFrame_recoverSymbol symbol graph bound saved)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (symbol::bound))
    simpa only [List.reverse_cons,List.length_cons,List.append_assoc,List.singleton_append] using all

private def countFrameBoundPassive (graph : List CountFrameSymbol) (i : Fin 8) : List CountFrameSymbol :=
  if i = 4 then graph else []

private noncomputable def countFrameBoundTranslated (graph : List CountFrameSymbol)
    (c : steinerEndpointUnaryBatchMachine.Cfg) : steinerGuardedUnaryGraphCountFrameMachine.Cfg :=
  StackIndexEmbedding.configuration countFrameBoundSlots (countFrameBoundPassive graph)
    (countFrameBoundTag.returningConfiguration .delimit c)

private theorem countFrame_boundStep (graph : List CountFrameSymbol) {c after : steinerEndpointUnaryBatchMachine.Cfg}
    (move : steinerEndpointUnaryBatchMachine.step c = some after) :
    steinerGuardedUnaryGraphCountFrameMachine.step (countFrameBoundTranslated graph c) =
      some (countFrameBoundTranslated graph after) := by
  have tagged := countFrameBoundTag.step_embedded_return .delimit
    (base := steinerEndpointUnaryBatchMachine.m) (host := countFrameBoundInner) (fun _ => rfl) move
  have framed := StackIndexEmbedding.step_on countFrameBoundSlots (base := countFrameBoundInner)
    (countFrameBoundPassive graph) (countFrameBoundTag.returningConfiguration .delimit c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem countFrame_boundTapes (graph : List CountFrameSymbol) (word : List (Option Bool))
    (c : steinerEndpointUnaryBatchMachine.Cfg) (tapes : c.stk = ![[],[],[],[],word,[]]) :
    (countFrameBoundTranslated graph c).stk = ![[],[],[],[],graph,word.map Sum.inr,[],[]] := by
  have image (i : Fin 6) : (countFrameBoundTranslated graph c).stk (countFrameBoundSlots i) =
      ((![[],[],[],[],word,[]] : Fin 6 → List (Option Bool)) i).map Sum.inr := by
    change StackIndexEmbedding.tapesAt countFrameBoundSlots (fun k => (c.stk k).map Sum.inr)
      (countFrameBoundPassive graph) (countFrameBoundSlots i) = _
    rw [StackIndexEmbedding.tapesAt_image,tapes]
  have extra (i : Fin 8) (absent : ∀ j, countFrameBoundSlots j ≠ i) :
      (countFrameBoundTranslated graph c).stk i = countFrameBoundPassive graph i :=
    StackIndexEmbedding.tapesAt_extra countFrameBoundSlots _ _ absent
  funext i
  fin_cases i
  · exact image 0
  · exact image 1
  · exact image 2
  · exact image 3
  · exact extra 4 (by intro j; fin_cases j <;> decide)
  · exact image 4
  · exact image 5
  · exact extra 7 (by intro j; fin_cases j <;> decide)

private theorem countFrame_boundInit (graph : List CountFrameSymbol) (input : List (Option Bool)) :
    countFrameBoundTranslated graph (initList steinerEndpointUnaryBatchMachine input) =
      countFrameCfg (some (.bound steinerEndpointUnaryBatchMachine.main)) [] graph (input.map Sum.inr) [] := by
  apply congrArg (fun stk : Fin 8 → List CountFrameSymbol =>
    (⟨some (.bound steinerEndpointUnaryBatchMachine.main),countFrameInitial,stk⟩ :
      steinerGuardedUnaryGraphCountFrameMachine.Cfg))
  apply countFrame_boundTapes
  funext i
  fin_cases i <;> rfl

private theorem countFrame_boundReturn (graph : List CountFrameSymbol) (out : List (Option Bool)) :
    countFrameBoundTranslated graph (haltList steinerEndpointUnaryBatchMachine out) =
      countFrameCfg (some .delimit) [] graph (out.map Sum.inr) [] := by
  apply congrArg (fun stk : Fin 8 → List CountFrameSymbol =>
    (⟨some .delimit,countFrameInitial,stk⟩ : steinerGuardedUnaryGraphCountFrameMachine.Cfg))
  apply countFrame_boundTapes
  funext i
  fin_cases i <;> rfl

private def countFrame_decodeBound {time : ℕ} (graph : List CountFrameSymbol) (input out : List (Option Bool))
    (run : TM2OutputsInTime steinerEndpointUnaryBatchMachine input (some out) time) :
    EvalsToInTime steinerGuardedUnaryGraphCountFrameMachine.step
      (countFrameCfg (some (.bound steinerEndpointUnaryBatchMachine.main)) [] graph (input.map Sum.inr) [])
      (some (countFrameCfg (some .delimit) [] graph (out.map Sum.inr) [])) time := by
  refine ⟨⟨run.steps,?_⟩,run.steps_le_m⟩
  have moved := iterate_map_some (countFrameBoundTranslated graph) (fun move => countFrame_boundStep graph move)
    run.steps run.evals_in_steps
  change (flip bind steinerGuardedUnaryGraphCountFrameMachine.step)^[run.steps]
    (some (countFrameBoundTranslated graph (initList steinerEndpointUnaryBatchMachine input))) =
    some (countFrameBoundTranslated graph (haltList steinerEndpointUnaryBatchMachine out)) at moved
  rwa [countFrame_boundInit,countFrame_boundReturn] at moved

private theorem countFrame_delimitStep (graph bound : List CountFrameSymbol) :
    steinerGuardedUnaryGraphCountFrameMachine.step (countFrameCfg (some .delimit) [] graph bound []) =
      some (countFrameCfg (some .prepend) [] (Sum.inr none::graph) bound []) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphCountFrameMachine,countFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    countFrameProgram,countFrameNext,countFrame_update4]
  rfl

private theorem countFrame_prependTally (graph bound : List CountFrameSymbol) :
    steinerGuardedUnaryGraphCountFrameMachine.step
      (countFrameCfg (some .prepend) [] graph (Sum.inr (some true)::bound) []) =
      some (countFrameCfg (some .prepend) [] (Sum.inr (some true)::graph) bound []) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphCountFrameMachine,countFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    countFrameProgram,countFrameObserve,countFrameNext,countFrame_update4,countFrame_update5]
  rfl

private theorem countFrame_prependEnd (graph : List CountFrameSymbol) :
    steinerGuardedUnaryGraphCountFrameMachine.step
      (countFrameCfg (some .prepend) [] graph [Sum.inr none] []) = some (countFrameCfg none [] graph [] []) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphCountFrameMachine,countFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    countFrameProgram,countFrameObserve,countFrame_update5]
  rfl

private def countFrameTallies (n : ℕ) : List CountFrameSymbol :=
  List.replicate n (Sum.inr (some true))

private def countFrame_prepend (n : ℕ) (graph : List CountFrameSymbol) :
    EvalsToInTime steinerGuardedUnaryGraphCountFrameMachine.step
      (countFrameCfg (some .prepend) [] graph (countFrameTallies n++[Sum.inr none]) [])
      (some (countFrameCfg none [] (countFrameTallies n++graph) [] [])) (n+1) := by
  induction n generalizing graph with
  | zero => exact countFrame_one (countFrame_prependEnd graph)
  | succ n ih =>
    have first := countFrame_one (countFrame_prependTally graph (countFrameTallies n++[Sum.inr none]))
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (Sum.inr (some true)::graph))
    have order : countFrameTallies n++Sum.inr (some true)::graph = countFrameTallies (n+1)++graph := by
      simp only [countFrameTallies,List.replicate_add,List.replicate_one,List.append_assoc,List.singleton_append]
    rw [order] at all
    exact all

private theorem countFrame_boundInput (bound : List Bool) :
    (encodeSteinerBinaryEndpointWords [bound]).map (Sum.inr : Option Bool → CountFrameSymbol) =
      countFrameUnaryBits bound++[Sum.inr none] := by
  simp only [encodeSteinerBinaryEndpointWords,List.flatMap_singleton]
  change ((bound.map some)++[none]).map Sum.inr = _
  simp only [List.map_append,List.map_singleton,List.map_map,countFrameUnaryBits]
  rfl

private theorem countFrame_boundOutput (n : ℕ) :
    (encodeSteinerUnaryEndpointValues [n]).map (Sum.inr : Option Bool → CountFrameSymbol) =
      countFrameTallies n++[Sum.inr none] := by
  rw [show encodeSteinerUnaryEndpointValues [n] = encodeSteinerBinaryEndpointWords [encodeSteinerUnaryProductCount n] from rfl,
    countFrame_boundInput]
  simp only [countFrameUnaryBits,countFrameTallies,encodeSteinerUnaryProductCount,List.map_replicate]

private def countFrame_assemble (bound : List Bool) (graph : List (Option Bool)) :
    let n := binaryWordValue bound
    EvalsToInTime steinerGuardedUnaryGraphCountFrameMachine.step
      (countFrameCfg (some .branchOnFlag) [] (graph.map Sum.inr) [] (countFrameUnaryBits bound).reverse)
      (some (countFrameCfg none [] (countFrameTallies n++Sum.inr none::graph.map Sum.inr) [] []))
      (5*bound.length+6*n+10) := by
  let n := binaryWordValue bound
  let tagged := graph.map (Sum.inr : Option Bool → CountFrameSymbol)
  have branched := countFrame_one (countFrame_acceptStep graph (countFrameUnaryBits bound).reverse)
  have recovered := countFrame_recover tagged [Sum.inr none] (countFrameUnaryBits bound).reverse
  rw [List.reverse_reverse,List.length_reverse,← countFrame_boundInput] at recovered
  have ready := EvalsToInTime.trans _ _ _ _ _ _ branched recovered
  have run := steinerEndpointUnaryBatchMachine_run [bound]
  have decoded := countFrame_decodeBound tagged _ _ run
  simp only [List.map_singleton,List.sum_singleton,encodeSteinerBinaryEndpointWords_length,List.length_singleton,
    countFrame_boundOutput] at decoded
  have converted := EvalsToInTime.trans _ _ _ _ _ _ ready decoded
  have separated := EvalsToInTime.trans _ _ _ _ _ _ converted
    (countFrame_one (countFrame_delimitStep tagged (countFrameTallies n++[Sum.inr none])))
  have all := EvalsToInTime.trans _ _ _ _ _ _ separated (countFrame_prepend n (Sum.inr none::tagged))
  refine ⟨all.toEvalsTo,?_⟩
  have paid := all.steps_le_m
  simp only [countFrameUnaryBits,List.length_map] at paid
  change all.steps ≤ 5*bound.length+6*n+10
  omega

private theorem countFrame_rejectStep (saved : List CountFrameSymbol) :
    steinerGuardedUnaryGraphCountFrameMachine.step (countFrameCfg (some .branchOnFlag) [] [Sum.inl none] [] saved) =
      some (countFrameCfg (some .discard) [] [Sum.inl none] [] saved) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphCountFrameMachine,countFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    countFrameProgram,countFrameObserve,countFrameNext,countFrameRejected]
  rfl

private theorem countFrame_discardSymbol (symbol : CountFrameSymbol) (saved : List CountFrameSymbol) :
    steinerGuardedUnaryGraphCountFrameMachine.step (countFrameCfg (some .discard) [] [Sum.inl none] [] (symbol::saved)) =
      some (countFrameCfg (some .discard) [] [Sum.inl none] [] saved) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphCountFrameMachine,countFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    countFrameProgram,countFrameObserve,countFrameNext,countFrame_update7]
  rfl

private theorem countFrame_discardEnd :
    steinerGuardedUnaryGraphCountFrameMachine.step (countFrameCfg (some .discard) [] [Sum.inl none] [] []) =
      some (countFrameCfg none [] [Sum.inl none] [] []) := by
  simp [FinTM2.step,steinerGuardedUnaryGraphCountFrameMachine,countFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    countFrameProgram,countFrameObserve,countFrame_update7]
  rfl

private def countFrame_discard (saved : List CountFrameSymbol) :
    EvalsToInTime steinerGuardedUnaryGraphCountFrameMachine.step
      (countFrameCfg (some .discard) [] [Sum.inl none] [] saved)
      (some (countFrameCfg none [] [Sum.inl none] [] [])) (saved.length+1) := by
  induction saved with
  | nil => exact countFrame_one countFrame_discardEnd
  | cons symbol saved ih =>
    exact EvalsToInTime.trans _ _ _ _ _ _ (countFrame_one (countFrame_discardSymbol symbol saved)) ih

private theorem countFrame_init (input : List CountFrameSymbol) :
    initList steinerGuardedUnaryGraphCountFrameMachine input = countFrameCfg (some .save) [] input [] [] := by
  apply congrArg (fun stk : Fin 8 → List CountFrameSymbol =>
    (⟨some .save,countFrameInitial,stk⟩ : steinerGuardedUnaryGraphCountFrameMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem countFrame_halt (out : List CountFrameSymbol) :
    haltList steinerGuardedUnaryGraphCountFrameMachine out = countFrameCfg none [] out [] [] := by
  apply congrArg (fun stk : Fin 8 → List CountFrameSymbol =>
    (⟨none,countFrameInitial,stk⟩ : steinerGuardedUnaryGraphCountFrameMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem countFrame_rawInput (bound : List Bool) (rows : List SteinerRangeWordPair) :
    encodeSteinerGuardedUnaryGraph bound rows = countFrameRawBits bound++Sum.inl (some none)::
      ((steinerRawGraphEndpointWords rows).flatMap encodeSteinerSingleBoundWord).map Sum.inl := by
  change ((bound.map fun b => some (some b))++[some none]++
    (steinerRawGraphEndpointWords rows).flatMap encodeSteinerSingleBoundWord).map Sum.inl = _
  simp only [List.map_append,List.map_map,List.append_assoc,List.singleton_append,countFrameRawBits]
  rfl

private def countFrame_ready (bound : List Bool) (rows : List SteinerRangeWordPair) :
    let input := encodeSteinerGuardedUnaryGraph bound rows
    EvalsToInTime steinerGuardedUnaryGraphCountFrameMachine.step
      (initList steinerGuardedUnaryGraphCountFrameMachine input)
      (some (countFrameCfg (some (.guard steinerGuardedUnaryGraphMachine.main)) [] input [] (countFrameUnaryBits bound).reverse))
      (2*bound.length+2) := by
  let tail := ((steinerRawGraphEndpointWords rows).flatMap encodeSteinerSingleBoundWord).map
    (Sum.inl : SteinerRawRangeSymbol → CountFrameSymbol)
  have saved := countFrame_save bound [] tail []
  simp only [List.append_nil] at saved
  have restored := countFrame_restore (countFrameRawBits bound).reverse (Sum.inl (some none)::tail)
    (countFrameUnaryBits bound).reverse
  simp only [List.reverse_reverse,List.length_reverse,countFrameRawBits,List.length_map] at restored
  have all := EvalsToInTime.trans _ _ _ _ _ _ saved restored
  change EvalsToInTime _ (initList steinerGuardedUnaryGraphCountFrameMachine _) _ _
  rw [countFrame_init,countFrame_rawInput]
  have paid := all.steps_le_m
  exact ⟨all.toEvalsTo,by omega⟩

private theorem countFrame_boundFits (bound : List Bool) (rows : List SteinerRangeWordPair) :
    bound.length ≤ (encodeSteinerGuardedUnaryGraph bound rows).length := by
  rw [encodeSteinerGuardedUnaryGraph_length]
  omega

/-- Emit the complete right-tagged count frame on acceptance. This
includes the vertex count even when the edge list is empty. -/
def steinerGuardedUnaryGraphCountFrameMachine_accepted {n : ℕ} (bound : List Bool) (number : binaryWordValue bound = n)
    (rows : List SteinerRangeWordPair) (decoded : List (Fin n × Fin n))
    (accepted : (decodeCheckedBinaryFinArcRowsWithWork (n+binaryEndpointBits rows) rows).1 = some decoded) :
    let X := (encodeSteinerGuardedUnaryGraph bound rows).length
    TM2OutputsInTime steinerGuardedUnaryGraphCountFrameMachine (encodeSteinerGuardedUnaryGraph bound rows)
      (some ((encodeSteinerUnaryGraphQueryFrame (n,decoded.map steinerUnaryArcValues)).map Sum.inr))
      (8*X^2+28*X+10*X*n+6*n+31) := by
  subst n
  let input := encodeSteinerGuardedUnaryGraph bound rows
  let X := input.length
  let n := binaryWordValue bound
  let endpoints := encodeSteinerUnaryEndpointValues (decoded.flatMap fun e => [e.1.val,e.2.val])
  have guard := steinerGuardedUnaryGraphMachine_vertex_time bound rows
  unfold steinerGuardedUnaryGraphAnswer at guard
  simp only [accepted] at guard
  have checked := countFrame_guard input (endpoints.map Sum.inr) (countFrameUnaryBits bound).reverse guard
  have prepared := EvalsToInTime.trans _ _ _ _ _ _ (countFrame_ready bound rows) checked
  have all := EvalsToInTime.trans _ _ _ _ _ _ prepared (countFrame_assemble bound endpoints)
  have framed : (encodeSteinerUnaryGraphQueryFrame (n,decoded.map steinerUnaryArcValues)).map
      (Sum.inr : Option Bool → CountFrameSymbol) = countFrameTallies n++Sum.inr none::endpoints.map Sum.inr := by
    simp only [encodeSteinerUnaryGraphQueryFrame,encodeSteinerUnaryArcEnumerationInput,
      List.map_append,List.map_cons,List.map_replicate,encodeSteinerUnaryArcRows_finite,countFrameTallies,endpoints]
  change EvalsToInTime steinerGuardedUnaryGraphCountFrameMachine.step _ (some (haltList _ _)) _
  rw [countFrame_halt,framed]
  refine ⟨all.toEvalsTo,?_⟩
  refine all.steps_le_m.trans ?_
  change (5*bound.length+6*n+10)+(8*X^2+21*X+10*(X*n)+19+(2*bound.length+2)) ≤
    8*X^2+28*X+10*X*n+6*n+31
  rw [← Nat.mul_assoc]
  have fits : bound.length ≤ X := countFrame_boundFits bound rows
  omega

/-- Rejection leaves a single left-tagged marker and discards the
saved word without converting its numeric value. -/
def steinerGuardedUnaryGraphCountFrameMachine_rejected {n : ℕ} (bound : List Bool) (number : binaryWordValue bound = n)
    (rows : List SteinerRangeWordPair)
    (rejected : (decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1 = none) :
    let X := (encodeSteinerGuardedUnaryGraph bound rows).length
    TM2OutputsInTime steinerGuardedUnaryGraphCountFrameMachine (encodeSteinerGuardedUnaryGraph bound rows)
      (some [Sum.inl none]) (8*X^2+19*X+17) := by
  let input := encodeSteinerGuardedUnaryGraph bound rows
  let X := input.length
  let saved := (countFrameUnaryBits bound).reverse
  have guard := steinerGuardedUnaryGraphMachine_rejected_time bound number rows rejected
  have checked := countFrame_guard input [Sum.inl none] saved guard
  have prepared := EvalsToInTime.trans _ _ _ _ _ _ (countFrame_ready bound rows) checked
  have decided := EvalsToInTime.trans _ _ _ _ _ _ prepared (countFrame_one (countFrame_rejectStep saved))
  have all := EvalsToInTime.trans _ _ _ _ _ _ decided (countFrame_discard saved)
  change EvalsToInTime steinerGuardedUnaryGraphCountFrameMachine.step _ (some (haltList _ _)) _
  rw [countFrame_halt]
  refine ⟨all.toEvalsTo,?_⟩
  have paid := all.steps_le_m
  simp only [saved,List.length_reverse,countFrameUnaryBits,List.length_map] at paid
  change all.steps ≤ (bound.length+1)+(1+(8*X^2+16*X+13+(2*bound.length+2))) at paid
  change all.steps ≤ 8*X^2+19*X+17
  have fits : bound.length ≤ X := countFrame_boundFits bound rows
  omega

/-- The guarded count frame keeps the supplied vertex count with its
decoded finite rows. A failed endpoint check returns the marker. -/
def steinerGuardedUnaryGraphCountFrameAnswer (bound : List Bool) (rows : List SteinerRangeWordPair) :
    List SteinerRawRangeSeedSymbol :=
  let n := binaryWordValue bound
  match (decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1 with
  | none => [Sum.inl none]
  | some decoded => (encodeSteinerUnaryGraphQueryFrame (n,decoded.map steinerUnaryArcValues)).map Sum.inr

/-- The general transition bound uses original length and numeric vertex
count. The separate rejection theorem depends only on original length. -/
def steinerGuardedUnaryGraphCountFrameMachine_run (bound : List Bool) (rows : List SteinerRangeWordPair) :
    let X := (encodeSteinerGuardedUnaryGraph bound rows).length
    let n := binaryWordValue bound
    TM2OutputsInTime steinerGuardedUnaryGraphCountFrameMachine (encodeSteinerGuardedUnaryGraph bound rows)
      (some (steinerGuardedUnaryGraphCountFrameAnswer bound rows)) (8*X^2+28*X+10*X*n+6*n+31) := by
  dsimp only
  unfold steinerGuardedUnaryGraphCountFrameAnswer
  dsimp only
  cases result : (decodeCheckedBinaryFinArcRowsWithWork (n := binaryWordValue bound)
      (binaryWordValue bound+binaryEndpointBits rows) rows).1 with
  | none =>
    let run := steinerGuardedUnaryGraphCountFrameMachine_rejected bound rfl rows result
    exact ⟨run.toEvalsTo,run.steps_le_m.trans (by omega)⟩
  | some decoded => exact steinerGuardedUnaryGraphCountFrameMachine_accepted bound rfl rows decoded result

end OnlineReachabilityPreservers
