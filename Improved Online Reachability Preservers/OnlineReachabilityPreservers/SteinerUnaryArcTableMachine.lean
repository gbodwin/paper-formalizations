import OnlineReachabilityPreservers.SteinerUnaryArcQueryMachine

/-! Answer an ordered batch of unary arc queries against one stored graph. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev ArcQueryLabel := steinerUnaryArcQueryMachine.Λ
private abbrev ArcQueryRegister := steinerUnaryArcQueryMachine.σ
private instance : Fintype ArcQueryLabel := steinerUnaryArcQueryMachine.ΛFin

private inductive ArcTableLabel where
  | readGraph
  | nextQuery
  | cloneGraph
  | restoreGraph
  | readQuery (second : Bool)
  | prefixQuery
  | query (label : ArcQueryLabel)
  | record
  | dropGraph
  | finish
  deriving Fintype

private abbrev ArcTableRegister := Option (Option Bool) × ArcQueryRegister
private abbrev ArcTableProgram := StackMachineTag.Program (Fin 8) (Option Bool) ArcTableLabel ArcTableRegister

private def arcTableInitial : ArcTableRegister := (none,steinerUnaryArcQueryMachine.initialState)

private def arcTableObserve (_ : ArcTableRegister) (seen : Option (Option Bool)) : ArcTableRegister :=
  (seen,steinerUnaryArcQueryMachine.initialState)

private def arcTableNext (label : ArcTableLabel) : ArcTableProgram :=
  load (fun _ => arcTableInitial) (goto (fun _ => label))

private def arcTableSymbol (r : ArcTableRegister) : Option Bool := r.1.getD none

private def arcTableTag :
    StackMachineTag (Option Bool) (Option Bool) ArcQueryLabel ArcTableLabel ArcQueryRegister ArcTableRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (none,r)
  readRegister := Prod.snd
  writeLabel := .query
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def arcTableSlots : Fin 4 ↪ Fin 8 :=
  ⟨fun i => ⟨i.val,i.isLt.trans (by decide)⟩,fun _ _ h => Fin.ext (congrArg (fun j : Fin 8 => j.val) h)⟩

private def arcTableInner :
    ArcTableLabel → StackMachineTag.Program (Fin 4) (Option Bool) ArcTableLabel ArcTableRegister
  | .query label => arcTableTag.returningStatement .record (steinerUnaryArcQueryMachine.m label)
  | _ => halt

private def arcTableTransfer (source target : Fin 8) (again next : ArcTableLabel) : ArcTableProgram :=
  pop source arcTableObserve <|
    branch (fun r => r.1.isSome)
      (push target arcTableSymbol (arcTableNext again))
      (arcTableNext next)

private def arcTableProgram : ArcTableLabel → ArcTableProgram
  | .readGraph =>
    pop 4 arcTableObserve <|
      branch (fun r => r.1 == some (some false))
        (arcTableNext .nextQuery)
        (push 5 arcTableSymbol (arcTableNext .readGraph))
  | .nextQuery =>
    peek 4 arcTableObserve <|
      branch (fun r => r.1.isSome) (arcTableNext .cloneGraph) (arcTableNext .dropGraph)
  | .cloneGraph =>
    pop 5 arcTableObserve <|
      branch (fun r => r.1.isSome)
        (push 0 arcTableSymbol (push 6 arcTableSymbol (arcTableNext .cloneGraph)))
        (arcTableNext .restoreGraph)
  | .restoreGraph => arcTableTransfer 6 5 .restoreGraph (.readQuery false)
  | .readQuery second =>
    pop 4 arcTableObserve <|
      push 6 arcTableSymbol <|
      branch (fun r => (arcTableSymbol r).isSome)
        (arcTableNext (.readQuery second))
        (arcTableNext (if second then .prefixQuery else .readQuery true))
  | .prefixQuery => arcTableTransfer 6 0 .prefixQuery (.query steinerUnaryArcQueryMachine.main)
  | .query label => StackIndexEmbedding.statement arcTableSlots (arcTableInner (.query label))
  | .record => pop 0 arcTableObserve (push 7 arcTableSymbol (arcTableNext .nextQuery))
  | .dropGraph =>
    pop 5 arcTableObserve <|
      branch (fun r => r.1.isSome) (arcTableNext .dropGraph) (arcTableNext .finish)
  | .finish =>
    pop 7 arcTableObserve <|
      branch (fun r => r.1.isSome)
        (push 4 arcTableSymbol (arcTableNext .finish))
        (load (fun _ => arcTableInitial) halt)

/-- Keep the graph in reverse order. Each query gets a new graph copy
and returns one Boolean while the remaining queries and graph stay parked. -/
abbrev steinerUnaryArcTableMachine : FinTM2 where
  K := Fin 8
  k₀ := 4
  k₁ := 4
  Γ _ := Option Bool
  Λ := ArcTableLabel
  main := .readGraph
  σ := ArcTableRegister
  initialState := arcTableInitial
  m := arcTableProgram

private def arcTableCfg (label : Option ArcTableLabel) (work input graph temp out : List (Option Bool)) :
    steinerUnaryArcTableMachine.Cfg where
  l := label
  var := arcTableInitial
  stk := ![work,[],[],[],input,graph,temp,out]

private theorem arcTable_update0 (w i g t a next : List (Option Bool)) :
    Function.update (![w,[],[],[],i,g,t,a] : Fin 8 → List (Option Bool)) 0 next = ![next,[],[],[],i,g,t,a] := by
  funext j
  fin_cases j <;> simp [Function.update]

private theorem arcTable_update4 (w i g t a next : List (Option Bool)) :
    Function.update (![w,[],[],[],i,g,t,a] : Fin 8 → List (Option Bool)) 4 next = ![w,[],[],[],next,g,t,a] := by
  funext j
  fin_cases j <;> simp [Function.update]

private theorem arcTable_update5 (w i g t a next : List (Option Bool)) :
    Function.update (![w,[],[],[],i,g,t,a] : Fin 8 → List (Option Bool)) 5 next = ![w,[],[],[],i,next,t,a] := by
  funext j
  fin_cases j <;> simp [Function.update]

private theorem arcTable_update6 (w i g t a next : List (Option Bool)) :
    Function.update (![w,[],[],[],i,g,t,a] : Fin 8 → List (Option Bool)) 6 next = ![w,[],[],[],i,g,next,a] := by
  funext j
  fin_cases j <;> simp [Function.update]

private theorem arcTable_update7 (w i g t a next : List (Option Bool)) :
    Function.update (![w,[],[],[],i,g,t,a] : Fin 8 → List (Option Bool)) 7 next = ![w,[],[],[],i,g,t,next] := by
  funext j
  fin_cases j <;> simp [Function.update]

private def arcTable_one {a b : steinerUnaryArcTableMachine.Cfg} (step : steinerUnaryArcTableMachine.step a = some b) :
    EvalsToInTime steinerUnaryArcTableMachine.step a (some b) 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := step

private theorem arcTable_readSymbol (s : Option Bool) (data graph : List (Option Bool)) (ordinary : s ≠ some false) :
    steinerUnaryArcTableMachine.step (arcTableCfg (some .readGraph) [] (s::data) graph [] []) =
      some (arcTableCfg (some .readGraph) [] data (s::graph) [] []) := by
  simp [FinTM2.step,steinerUnaryArcTableMachine,arcTableCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcTableProgram,arcTableObserve,arcTableSymbol,arcTableNext,arcTable_update4,arcTable_update5,ordinary]
  rfl

private theorem arcTable_readEnd (data graph : List (Option Bool)) :
    steinerUnaryArcTableMachine.step (arcTableCfg (some .readGraph) [] (some false::data) graph [] []) =
      some (arcTableCfg (some .nextQuery) [] data graph [] []) := by
  simp [FinTM2.step,steinerUnaryArcTableMachine,arcTableCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcTableProgram,arcTableObserve,arcTableNext,arcTable_update4]
  rfl

private def arcTable_read (word input graph : List (Option Bool)) (ordinary : some false ∉ word) :
    EvalsToInTime steinerUnaryArcTableMachine.step
      (arcTableCfg (some .readGraph) [] (word++some false::input) graph [] [])
      (some (arcTableCfg (some .nextQuery) [] input (word.reverse++graph) [] [])) (word.length+1) := by
  induction word generalizing graph with
  | nil => exact arcTable_one (arcTable_readEnd input graph)
  | cons s word ih =>
    have symbol : s ≠ some false := fun equal => ordinary (equal ▸ List.mem_cons_self)
    have tail : some false ∉ word := fun present => ordinary (List.mem_cons_of_mem _ present)
    have first := arcTable_one (arcTable_readSymbol s (word++some false::input) graph symbol)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (s::graph) tail)
    simpa only [List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,List.nil_append,
      List.length_cons] using all

private theorem arcTable_startQuery (s : Option Bool) (input graph out : List (Option Bool)) :
    steinerUnaryArcTableMachine.step (arcTableCfg (some .nextQuery) [] (s::input) graph [] out) =
      some (arcTableCfg (some .cloneGraph) [] (s::input) graph [] out) := by
  simp [FinTM2.step,steinerUnaryArcTableMachine,arcTableCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcTableProgram,arcTableObserve,arcTableNext]
  rfl

private theorem arcTable_endQueries (graph out : List (Option Bool)) :
    steinerUnaryArcTableMachine.step (arcTableCfg (some .nextQuery) [] [] graph [] out) =
      some (arcTableCfg (some .dropGraph) [] [] graph [] out) := by
  simp [FinTM2.step,steinerUnaryArcTableMachine,arcTableCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcTableProgram,arcTableObserve,arcTableNext]
  rfl

private theorem arcTable_cloneSymbol (s : Option Bool) (work input graph temp out : List (Option Bool)) :
    steinerUnaryArcTableMachine.step (arcTableCfg (some .cloneGraph) work input (s::graph) temp out) =
      some (arcTableCfg (some .cloneGraph) (s::work) input graph (s::temp) out) := by
  simp [FinTM2.step,steinerUnaryArcTableMachine,arcTableCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcTableProgram,arcTableObserve,arcTableSymbol,arcTableNext,arcTable_update0,arcTable_update5,arcTable_update6]
  rfl

private theorem arcTable_cloneEnd (work input temp out : List (Option Bool)) :
    steinerUnaryArcTableMachine.step (arcTableCfg (some .cloneGraph) work input [] temp out) =
      some (arcTableCfg (some .restoreGraph) work input [] temp out) := by
  simp [FinTM2.step,steinerUnaryArcTableMachine,arcTableCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcTableProgram,arcTableObserve,arcTableNext,arcTable_update5]
  rfl

private def arcTable_clone (graph work input temp out : List (Option Bool)) :
    EvalsToInTime steinerUnaryArcTableMachine.step
      (arcTableCfg (some .cloneGraph) work input graph temp out)
      (some (arcTableCfg (some .restoreGraph) (graph.reverse++work) input [] (graph.reverse++temp) out))
      (graph.length+1) := by
  induction graph generalizing work temp with
  | nil => exact arcTable_one (arcTable_cloneEnd work input temp out)
  | cons s graph ih =>
    have first := arcTable_one (arcTable_cloneSymbol s work input graph temp out)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (s::work) (s::temp))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons] using all

private theorem arcTable_restoreSymbol (s : Option Bool) (work input graph temp out : List (Option Bool)) :
    steinerUnaryArcTableMachine.step (arcTableCfg (some .restoreGraph) work input graph (s::temp) out) =
      some (arcTableCfg (some .restoreGraph) work input (s::graph) temp out) := by
  simp [FinTM2.step,steinerUnaryArcTableMachine,arcTableCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcTableProgram,arcTableTransfer,arcTableObserve,arcTableSymbol,arcTableNext,arcTable_update5,arcTable_update6]
  rfl

private theorem arcTable_restoreEnd (work input graph out : List (Option Bool)) :
    steinerUnaryArcTableMachine.step (arcTableCfg (some .restoreGraph) work input graph [] out) =
      some (arcTableCfg (some (.readQuery false)) work input graph [] out) := by
  simp [FinTM2.step,steinerUnaryArcTableMachine,arcTableCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcTableProgram,arcTableTransfer,arcTableObserve,arcTableNext,arcTable_update6]
  rfl

private def arcTable_restore (temp work input graph out : List (Option Bool)) :
    EvalsToInTime steinerUnaryArcTableMachine.step
      (arcTableCfg (some .restoreGraph) work input graph temp out)
      (some (arcTableCfg (some (.readQuery false)) work input (temp.reverse++graph) [] out))
      (temp.length+1) := by
  induction temp generalizing graph with
  | nil => exact arcTable_one (arcTable_restoreEnd work input graph out)
  | cons s temp ih =>
    have first := arcTable_one (arcTable_restoreSymbol s work input graph temp out)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (s::graph))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons] using all

private theorem arcTable_fieldTally (second : Bool) (work input graph temp out : List (Option Bool)) :
    steinerUnaryArcTableMachine.step (arcTableCfg (some (.readQuery second)) work (some true::input) graph temp out) =
      some (arcTableCfg (some (.readQuery second)) work input graph (some true::temp) out) := by
  simp [FinTM2.step,steinerUnaryArcTableMachine,arcTableCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcTableProgram,arcTableObserve,arcTableSymbol,arcTableNext,arcTable_update4,arcTable_update6]
  rfl

private theorem arcTable_fieldEnd (second : Bool) (work input graph temp out : List (Option Bool)) :
    steinerUnaryArcTableMachine.step (arcTableCfg (some (.readQuery second)) work (none::input) graph temp out) =
      some (arcTableCfg (some (if second then .prefixQuery else .readQuery true)) work input graph (none::temp) out) := by
  simp [FinTM2.step,steinerUnaryArcTableMachine,arcTableCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcTableProgram,arcTableObserve,arcTableSymbol,arcTableNext,arcTable_update4,arcTable_update6]
  rfl

private abbrev arcTableTallies (n : ℕ) : List (Option Bool) := List.replicate n (some true)

private def arcTable_readField (second : Bool) (field : ℕ) (work input graph temp out : List (Option Bool)) :
    EvalsToInTime steinerUnaryArcTableMachine.step
      (arcTableCfg (some (.readQuery second)) work (arcTableTallies field++none::input) graph temp out)
      (some (arcTableCfg (some (if second then .prefixQuery else .readQuery true)) work input graph
        ((arcTableTallies field++[none]).reverse++temp) out)) (field+1) := by
  induction field generalizing temp with
  | zero => exact arcTable_one (arcTable_fieldEnd second work input graph temp out)
  | succ field ih =>
    have first := arcTable_one (arcTable_fieldTally second work (arcTableTallies field++none::input) graph temp out)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (some true::temp))
    simpa only [List.replicate_succ,List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,
      List.nil_append] using all

private theorem arcTable_prefixSymbol (s : Option Bool) (work input graph temp out : List (Option Bool)) :
    steinerUnaryArcTableMachine.step (arcTableCfg (some .prefixQuery) work input graph (s::temp) out) =
      some (arcTableCfg (some .prefixQuery) (s::work) input graph temp out) := by
  simp [FinTM2.step,steinerUnaryArcTableMachine,arcTableCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcTableProgram,arcTableTransfer,arcTableObserve,arcTableSymbol,arcTableNext,arcTable_update0,arcTable_update6]
  rfl

private theorem arcTable_prefixEnd (work input graph out : List (Option Bool)) :
    steinerUnaryArcTableMachine.step (arcTableCfg (some .prefixQuery) work input graph [] out) =
      some (arcTableCfg (some (.query steinerUnaryArcQueryMachine.main)) work input graph [] out) := by
  simp [FinTM2.step,steinerUnaryArcTableMachine,arcTableCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcTableProgram,arcTableTransfer,arcTableObserve,arcTableNext,arcTable_update6]
  rfl

private def arcTable_prefix (temp work input graph out : List (Option Bool)) :
    EvalsToInTime steinerUnaryArcTableMachine.step
      (arcTableCfg (some .prefixQuery) work input graph temp out)
      (some (arcTableCfg (some (.query steinerUnaryArcQueryMachine.main)) (temp.reverse++work) input graph [] out))
      (temp.length+1) := by
  induction temp generalizing work with
  | nil => exact arcTable_one (arcTable_prefixEnd work input graph out)
  | cons s temp ih =>
    have first := arcTable_one (arcTable_prefixSymbol s work input graph temp out)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (s::work))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons] using all

private theorem arcTable_record (answer : Bool) (input graph out : List (Option Bool)) :
    steinerUnaryArcTableMachine.step (arcTableCfg (some .record) [some answer] input graph [] out) =
      some (arcTableCfg (some .nextQuery) [] input graph [] (some answer::out)) := by
  simp [FinTM2.step,steinerUnaryArcTableMachine,arcTableCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcTableProgram,arcTableObserve,arcTableSymbol,arcTableNext,arcTable_update0,arcTable_update7]
  rfl

private theorem arcTable_dropSymbol (s : Option Bool) (graph out : List (Option Bool)) :
    steinerUnaryArcTableMachine.step (arcTableCfg (some .dropGraph) [] [] (s::graph) [] out) =
      some (arcTableCfg (some .dropGraph) [] [] graph [] out) := by
  simp [FinTM2.step,steinerUnaryArcTableMachine,arcTableCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcTableProgram,arcTableObserve,arcTableNext,arcTable_update5]
  rfl

private theorem arcTable_dropEnd (out : List (Option Bool)) :
    steinerUnaryArcTableMachine.step (arcTableCfg (some .dropGraph) [] [] [] [] out) =
      some (arcTableCfg (some .finish) [] [] [] [] out) := by
  simp [FinTM2.step,steinerUnaryArcTableMachine,arcTableCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcTableProgram,arcTableObserve,arcTableNext,arcTable_update5]
  rfl

private def arcTable_drop (graph out : List (Option Bool)) :
    EvalsToInTime steinerUnaryArcTableMachine.step
      (arcTableCfg (some .dropGraph) [] [] graph [] out)
      (some (arcTableCfg (some .finish) [] [] [] [] out)) (graph.length+1) := by
  induction graph with
  | nil => exact arcTable_one (arcTable_dropEnd out)
  | cons s graph ih => exact EvalsToInTime.trans _ _ _ _ _ _ (arcTable_one (arcTable_dropSymbol s graph out)) ih

private theorem arcTable_finishSymbol (s : Option Bool) (input out : List (Option Bool)) :
    steinerUnaryArcTableMachine.step (arcTableCfg (some .finish) [] input [] [] (s::out)) =
      some (arcTableCfg (some .finish) [] (s::input) [] [] out) := by
  simp [FinTM2.step,steinerUnaryArcTableMachine,arcTableCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcTableProgram,arcTableObserve,arcTableSymbol,arcTableNext,arcTable_update4,arcTable_update7]
  rfl

private theorem arcTable_finishEnd (input : List (Option Bool)) :
    steinerUnaryArcTableMachine.step (arcTableCfg (some .finish) [] input [] [] []) =
      some (arcTableCfg none [] input [] [] []) := by
  simp [FinTM2.step,steinerUnaryArcTableMachine,arcTableCfg,Turing.TM2.step,Turing.TM2.stepAux,
    arcTableProgram,arcTableObserve,arcTable_update7]
  rfl

private def arcTable_finish (out input : List (Option Bool)) :
    EvalsToInTime steinerUnaryArcTableMachine.step
      (arcTableCfg (some .finish) [] input [] [] out)
      (some (arcTableCfg none [] (out.reverse++input) [] [] [])) (out.length+1) := by
  induction out generalizing input with
  | nil => exact arcTable_one (arcTable_finishEnd input)
  | cons s out ih =>
    have first := arcTable_one (arcTable_finishSymbol s input out)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (s::input))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons] using all

private def arcTableExtra (input graph out : List (Option Bool)) : Fin 8 → List (Option Bool) :=
  ![[],[],[],[],input,graph,[],out]

private noncomputable def arcTableTranslated (input graph out : List (Option Bool)) (c : steinerUnaryArcQueryMachine.Cfg) :
    steinerUnaryArcTableMachine.Cfg :=
  StackIndexEmbedding.configuration arcTableSlots (arcTableExtra input graph out)
    (arcTableTag.returningConfiguration .record c)

private theorem arcTable_queryStep (input graph out : List (Option Bool)) {c after : steinerUnaryArcQueryMachine.Cfg}
    (move : steinerUnaryArcQueryMachine.step c = some after) :
    steinerUnaryArcTableMachine.step (arcTableTranslated input graph out c) =
      some (arcTableTranslated input graph out after) := by
  have tagged := arcTableTag.step_embedded_return .record (base := steinerUnaryArcQueryMachine.m)
    (host := arcTableInner) (fun _ => rfl) move
  have framed := StackIndexEmbedding.step_on arcTableSlots (base := arcTableInner)
    (arcTableExtra input graph out) (arcTableTag.returningConfiguration .record c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem arcTable_translatedTapes (input graph out word : List (Option Bool))
    (c : steinerUnaryArcQueryMachine.Cfg) (tapes : c.stk = ![word,[],[],[]]) :
    (arcTableTranslated input graph out c).stk = ![word,[],[],[],input,graph,[],out] := by
  have image (j : Fin 4) : (arcTableTranslated input graph out c).stk (arcTableSlots j) =
      (![word,[],[],[]] : Fin 4 → List (Option Bool)) j := by
    change StackIndexEmbedding.tapesAt arcTableSlots (fun i => (c.stk i).map id) _ (arcTableSlots j) = _
    rw [StackIndexEmbedding.tapesAt_image,List.map_id,tapes]
  have extra (j : Fin 8) (outside : ∀ i, arcTableSlots i ≠ j) :
      (arcTableTranslated input graph out c).stk j = arcTableExtra input graph out j := by
    exact StackIndexEmbedding.tapesAt_extra arcTableSlots _ _ outside
  funext j
  fin_cases j
  · exact image 0
  · exact image 1
  · exact image 2
  · exact image 3
  · exact extra 4 (by intro i; fin_cases i <;> decide)
  · exact extra 5 (by intro i; fin_cases i <;> decide)
  · exact extra 6 (by intro i; fin_cases i <;> decide)
  · exact extra 7 (by intro i; fin_cases i <;> decide)

private theorem arcTable_queryInit (word input graph out : List (Option Bool)) :
    arcTableTranslated input graph out (initList steinerUnaryArcQueryMachine word) =
      arcTableCfg (some (.query steinerUnaryArcQueryMachine.main)) word input graph [] out := by
  apply congrArg (fun stk : Fin 8 → List (Option Bool) =>
    (⟨some (.query steinerUnaryArcQueryMachine.main),arcTableInitial,stk⟩ : steinerUnaryArcTableMachine.Cfg))
  apply arcTable_translatedTapes
  funext i
  fin_cases i <;> rfl

private theorem arcTable_queryReturn (word input graph out : List (Option Bool)) :
    arcTableTranslated input graph out (haltList steinerUnaryArcQueryMachine word) =
      arcTableCfg (some .record) word input graph [] out := by
  apply congrArg (fun stk : Fin 8 → List (Option Bool) =>
    (⟨some .record,arcTableInitial,stk⟩ : steinerUnaryArcTableMachine.Cfg))
  apply arcTable_translatedTapes
  funext i
  fin_cases i <;> rfl

private def arcTable_query (request : SteinerUnaryArcQuery) (input graph out : List (Option Bool)) :
    EvalsToInTime steinerUnaryArcTableMachine.step
      (arcTableCfg (some (.query steinerUnaryArcQueryMachine.main)) (encodeSteinerUnaryArcQuery request) input graph [] out)
      (some (arcTableCfg (some .record) (steinerUnaryArcQueryAnswer request) input graph [] out))
      (3*(encodeSteinerUnaryArcQuery request).length+1) := by
  let run := steinerUnaryArcQueryMachine_run request
  refine ⟨⟨run.steps,?_⟩,run.steps_le_m⟩
  have executed := iterate_map_some (arcTableTranslated input graph out) (fun move => arcTable_queryStep input graph out move)
    run.steps run.evals_in_steps
  change (flip bind steinerUnaryArcTableMachine.step)^[run.steps]
      (some (arcTableTranslated input graph out (initList steinerUnaryArcQueryMachine (encodeSteinerUnaryArcQuery request)))) =
    some (arcTableTranslated input graph out (haltList steinerUnaryArcQueryMachine (steinerUnaryArcQueryAnswer request))) at executed
  rwa [arcTable_queryInit,arcTable_queryReturn] at executed

private theorem arcTable_frame (a b : ℕ) (rows : List (ℕ × ℕ)) :
    encodeSteinerUnaryArcRows ((a,b)::rows) =
      (arcTableTallies a++[none])++(arcTableTallies b++[none])++encodeSteinerUnaryArcRows rows := by
  rw [encodeSteinerUnaryArcRows_cons]
  simp only [List.append_assoc,List.cons_append,List.nil_append]

private theorem arcTable_noSeparator (rows : List (ℕ × ℕ)) : some false ∉ encodeSteinerUnaryArcRows rows := by
  induction rows with
  | nil => exact List.not_mem_nil
  | cons row rows ih =>
    obtain ⟨a,b⟩ := row
    rw [encodeSteinerUnaryArcRows_cons]
    simp [List.mem_replicate,ih]

private def arcTable_prepare (a b : ℕ) (graph later : List (ℕ × ℕ)) (out : List (Option Bool)) :
    let saved := encodeSteinerUnaryArcRows graph
    let query := encodeSteinerUnaryArcRows [(a,b)]
    EvalsToInTime steinerUnaryArcTableMachine.step
      (arcTableCfg (some .nextQuery) [] (encodeSteinerUnaryArcRows ((a,b)::later)) saved.reverse [] out)
      (some (arcTableCfg (some (.query steinerUnaryArcQueryMachine.main))
        (encodeSteinerUnaryArcQuery ((a,b),graph)) (encodeSteinerUnaryArcRows later) saved.reverse [] out))
      (2*saved.length+2*query.length+4) := by
  dsimp only
  let saved := encodeSteinerUnaryArcRows graph
  let input := encodeSteinerUnaryArcRows later
  let left := arcTableTallies a++[none]
  let right := arcTableTallies b++[none]
  let query := encodeSteinerUnaryArcRows [(a,b)]
  have front : query = left++right := by
    dsimp only [query]
    rw [arcTable_frame]
    rw [show encodeSteinerUnaryArcRows [] = [] from rfl,List.append_nil]
  let startInput := encodeSteinerUnaryArcRows ((a,b)::later)
  have sameFrame : startInput = arcTableTallies a++none::(arcTableTallies b++none::input) :=
    encodeSteinerUnaryArcRows_cons a b later
  have start : steinerUnaryArcTableMachine.step (arcTableCfg (some .nextQuery) [] startInput saved.reverse [] out) =
      some (arcTableCfg (some .cloneGraph) [] startInput saved.reverse [] out) := by
    dsimp only [startInput]
    rw [encodeSteinerUnaryArcRows_cons]
    cases a with
    | zero => exact arcTable_startQuery _ _ _ _
    | succ a =>
      simpa only [List.replicate_succ,List.cons_append] using
        arcTable_startQuery (some true) (arcTableTallies a++none::(arcTableTallies b++none::input)) saved.reverse out
  have copied := arcTable_clone saved.reverse [] startInput [] out
  rw [List.reverse_reverse,List.length_reverse,List.append_nil] at copied
  have reparked := arcTable_restore saved saved startInput [] out
  rw [List.append_nil] at reparked
  have readLeft := arcTable_readField false a saved (arcTableTallies b++none::input) saved.reverse [] out
  have readRight := arcTable_readField true b saved input saved.reverse left.reverse out
  simp only [List.append_nil,Bool.false_eq_true,ite_false] at readLeft
  simp only [ite_true] at readRight
  rw [← sameFrame] at readLeft
  have began := EvalsToInTime.trans _ _ _ _ _ _ (arcTable_one start) copied
  have parked := EvalsToInTime.trans _ _ _ _ _ _ began reparked
  have movedLeft := EvalsToInTime.trans _ _ _ _ _ _ parked readLeft
  have movedBoth := EvalsToInTime.trans _ _ _ _ _ _ movedLeft readRight
  change EvalsToInTime steinerUnaryArcTableMachine.step _
    (some (arcTableCfg (some .prefixQuery) saved input saved.reverse (right.reverse++left.reverse) out)) _ at movedBoth
  rw [← List.reverse_append,← front] at movedBoth
  have prefixed := arcTable_prefix query.reverse saved input saved.reverse out
  rw [List.reverse_reverse,List.length_reverse] at prefixed
  have all := EvalsToInTime.trans _ _ _ _ _ _ movedBoth prefixed
  rw [encodeSteinerUnaryArcQuery_append]
  refine ⟨all.toEvalsTo,all.steps_le_m.trans ?_⟩
  have length : query.length = a+b+2 := by
    rw [front]
    simp only [left,right,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
    omega
  change _ ≤ 2*saved.length+2*query.length+4
  omega

private def arcTable_single (a b : ℕ) (graph later : List (ℕ × ℕ)) (out : List (Option Bool)) :
    let saved := encodeSteinerUnaryArcRows graph
    let query := encodeSteinerUnaryArcRows [(a,b)]
    EvalsToInTime steinerUnaryArcTableMachine.step
      (arcTableCfg (some .nextQuery) [] (encodeSteinerUnaryArcRows ((a,b)::later)) saved.reverse [] out)
      (some (arcTableCfg (some .nextQuery) [] (encodeSteinerUnaryArcRows later) saved.reverse []
        (some (decide ((a,b) ∈ graph))::out))) (5*saved.length+5*query.length+6) := by
  dsimp only
  let saved := encodeSteinerUnaryArcRows graph
  let query := encodeSteinerUnaryArcRows [(a,b)]
  let laterFrame := encodeSteinerUnaryArcRows later
  let found := decide ((a,b) ∈ graph)
  have prepared := arcTable_prepare a b graph later out
  have queried := arcTable_query ((a,b),graph) laterFrame saved.reverse out
  have spentQuery : (encodeSteinerUnaryArcQuery ((a,b),graph)).length = query.length+saved.length := by
    rw [encodeSteinerUnaryArcQuery_append,List.length_append]
  rw [spentQuery] at queried
  have evaluated := EvalsToInTime.trans _ _ _ _ _ _ prepared queried
  have all := EvalsToInTime.trans _ _ _ _ _ _ evaluated (arcTable_one (arcTable_record found laterFrame saved.reverse out))
  exact ⟨all.toEvalsTo,by
    have spent := all.steps_le_m
    dsimp only [query,saved] at spent
    omega⟩

abbrev SteinerUnaryArcTable := List (ℕ × ℕ) × List (ℕ × ℕ)

/-- A false symbol separates the archived graph from the ordered query rows. -/
def encodeSteinerUnaryArcTable (request : SteinerUnaryArcTable) : List (Option Bool) :=
  encodeSteinerUnaryArcRows request.1++some false::encodeSteinerUnaryArcRows request.2

/-- Return exactly one membership bit per query, in input order. -/
def steinerUnaryArcTableAnswer (request : SteinerUnaryArcTable) : List (Option Bool) :=
  request.2.map fun arc => some (decide (arc ∈ request.1))

private def arcTable_queries (graph queries : List (ℕ × ℕ)) (out : List (Option Bool)) :
    let saved := encodeSteinerUnaryArcRows graph
    let input := encodeSteinerUnaryArcRows queries
    EvalsToInTime steinerUnaryArcTableMachine.step (arcTableCfg (some .nextQuery) [] input saved.reverse [] out)
      (some (arcTableCfg (some .dropGraph) [] [] saved.reverse []
        ((steinerUnaryArcTableAnswer (graph,queries)).reverse++out)))
      ((5*saved.length+6)*queries.length+5*input.length+1) := by
  dsimp only
  induction queries generalizing out with
  | nil =>
    have first := arcTable_one (arcTable_endQueries (encodeSteinerUnaryArcRows graph).reverse out)
    simpa only [steinerUnaryArcTableAnswer,List.map_nil,List.reverse_nil,List.nil_append,List.length_nil,
      Nat.mul_zero,Nat.zero_add,show encodeSteinerUnaryArcRows [] = [] from rfl] using first
  | cons arc queries ih =>
    obtain ⟨a,b⟩ := arc
    let found := decide ((a,b) ∈ graph)
    have first := arcTable_single a b graph queries out
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (some found::out))
    have layout := congrArg List.length (encodeSteinerUnaryArcRows_append [(a,b)] queries)
    simp only [List.length_append] at layout
    change (encodeSteinerUnaryArcRows ((a,b)::queries)).length = _ at layout
    refine ⟨⟨all.steps,?_⟩,all.steps_le_m.trans ?_⟩
    · simpa only [steinerUnaryArcTableAnswer,Prod.snd,Prod.fst,List.map_cons,List.reverse_cons,List.append_assoc,
        List.singleton_append,List.nil_append,found] using all.evals_in_steps
    · simp only [layout,List.length_cons,Nat.mul_succ]
      omega

private theorem arcTable_init (word : List (Option Bool)) :
    initList steinerUnaryArcTableMachine word = arcTableCfg (some .readGraph) [] word [] [] [] := by
  apply congrArg (fun stk : Fin 8 → List (Option Bool) =>
    (⟨some .readGraph,arcTableInitial,stk⟩ : steinerUnaryArcTableMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem arcTable_halt (word : List (Option Bool)) :
    haltList steinerUnaryArcTableMachine word = arcTableCfg none [] word [] [] [] := by
  apply congrArg (fun stk : Fin 8 → List (Option Bool) =>
    (⟨none,arcTableInitial,stk⟩ : steinerUnaryArcTableMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- For graph frame length G, query frame length Q, and q queries,
 the ordered decision table takes at most `2G + 5Q + (5G+7)q + 4` steps. -/
def steinerUnaryArcTableMachine_run (request : SteinerUnaryArcTable) :
    let G := (encodeSteinerUnaryArcRows request.1).length
    let Q := (encodeSteinerUnaryArcRows request.2).length
    TM2OutputsInTime steinerUnaryArcTableMachine (encodeSteinerUnaryArcTable request)
      (some (steinerUnaryArcTableAnswer request)) (2*G+5*Q+(5*G+7)*request.2.length+4) := by
  rcases request with ⟨graph,queries⟩
  let saved := encodeSteinerUnaryArcRows graph
  let input := encodeSteinerUnaryArcRows queries
  let answer := steinerUnaryArcTableAnswer (graph,queries)
  have read := arcTable_read saved input [] (arcTable_noSeparator graph)
  rw [List.append_nil] at read
  have evaluated := arcTable_queries graph queries []
  rw [List.append_nil] at evaluated
  have paid := EvalsToInTime.trans _ _ _ _ _ _ read evaluated
  have dropped := arcTable_drop saved.reverse answer.reverse
  rw [List.length_reverse] at dropped
  have cleaned := EvalsToInTime.trans _ _ _ _ _ _ paid dropped
  have finished := arcTable_finish answer.reverse []
  rw [List.reverse_reverse,List.append_nil,List.length_reverse] at finished
  have all := EvalsToInTime.trans _ _ _ _ _ _ cleaned finished
  change EvalsToInTime steinerUnaryArcTableMachine.step
    (initList steinerUnaryArcTableMachine (encodeSteinerUnaryArcTable (graph,queries)))
    (some (haltList steinerUnaryArcTableMachine answer)) _
  rw [arcTable_init,arcTable_halt]
  refine ⟨all.toEvalsTo,all.steps_le_m.trans ?_⟩
  have outputCount : answer.length = queries.length := by simp [answer,steinerUnaryArcTableAnswer]
  dsimp only [saved,input] at *
  rw [outputCount]
  simp only [Nat.add_mul]
  omega

private theorem arcTable_frameLength_le (rows : List (ℕ × ℕ)) : rows.length ≤ (encodeSteinerUnaryArcRows rows).length := by
  induction rows with
  | nil => exact Nat.zero_le _
  | cons arc rows ih =>
    obtain ⟨a,b⟩ := arc
    rw [encodeSteinerUnaryArcRows_cons]
    simp only [List.length_append,List.length_cons,List.length_replicate]
    omega

/-- The repeated graph scan is quadratic in the whole encoded input. -/
def steinerUnaryArcTableMachine_quadratic (request : SteinerUnaryArcTable) :
    let X := (encodeSteinerUnaryArcTable request).length
    TM2OutputsInTime steinerUnaryArcTableMachine (encodeSteinerUnaryArcTable request)
      (some (steinerUnaryArcTableAnswer request)) (5*X^2+14*X+4) := by
  dsimp only
  let G := (encodeSteinerUnaryArcRows request.1).length
  let Q := (encodeSteinerUnaryArcRows request.2).length
  let X := (encodeSteinerUnaryArcTable request).length
  let q := request.2.length
  have layout : X = G+1+Q := by simp [X,G,Q,encodeSteinerUnaryArcTable]; omega
  have count : q ≤ Q := arcTable_frameLength_le request.2
  have scans : G*q ≤ X^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have run := steinerUnaryArcTableMachine_run request
  refine ⟨run.toEvalsTo,run.steps_le_m.trans ?_⟩
  change 2*G+5*Q+(5*G+7)*q+4 ≤ 5*X^2+14*X+4
  rw [Nat.add_mul,Nat.mul_assoc]
  omega

/-- This polynomial bounds the actual eight-stack table machine. -/
noncomputable def steinerUnaryArcTableMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryArcTable id steinerUnaryArcTableAnswer where
  tm := steinerUnaryArcTableMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 5*Polynomial.X^2+Polynomial.C 14*Polynomial.X+Polynomial.C 4
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,
      Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_pow] using steinerUnaryArcTableMachine_quadratic request

/-- Finite query indices and all accepted graph rows use the same
numerical encoding. The output table is membership in the finite graph. -/
def steinerUnaryArcTableMachine_finset {n : ℕ} (rows queries : List (Fin n × Fin n)) :
    let request : SteinerUnaryArcTable := (rows.map steinerUnaryArcValues,queries.map steinerUnaryArcValues)
    let X := (encodeSteinerUnaryArcTable request).length
    TM2OutputsInTime steinerUnaryArcTableMachine (encodeSteinerUnaryArcTable request)
      (some (queries.map fun arc => some (decide (arc ∈ rows.toFinset)))) (5*X^2+14*X+4) := by
  let request : SteinerUnaryArcTable := (rows.map steinerUnaryArcValues,queries.map steinerUnaryArcValues)
  have answer : steinerUnaryArcTableAnswer request = queries.map (fun arc => some (decide (arc ∈ rows.toFinset))) := by
    change (queries.map steinerUnaryArcValues).map (fun arc => some (decide (arc ∈ rows.map steinerUnaryArcValues))) = _
    rw [List.map_map]
    congr 1
    funext arc
    change some (decide (steinerUnaryArcValues arc ∈ rows.map steinerUnaryArcValues)) = _
    simp only [steinerUnaryArcValues_mem_finset]
  rw [← answer]
  exact steinerUnaryArcTableMachine_quadratic request

end OnlineReachabilityPreservers
