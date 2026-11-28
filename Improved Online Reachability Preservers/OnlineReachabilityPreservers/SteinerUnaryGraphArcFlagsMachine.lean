import OnlineReachabilityPreservers.SteinerUnaryGraphArcCountMachine

/-! Retain the full ordered adjacency flags from the unary graph frame. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing

private abbrev ArcFlagsPrepLabel := steinerUnaryGraphQueryFrameMachine.Λ
private abbrev ArcFlagsPrepRegister := steinerUnaryGraphQueryFrameMachine.σ
private abbrev ArcFlagsTableLabel := steinerUnaryArcTableMachine.Λ
private abbrev ArcFlagsTableRegister := steinerUnaryArcTableMachine.σ
private instance : Fintype ArcFlagsPrepLabel := steinerUnaryGraphQueryFrameMachine.ΛFin
private instance : Fintype ArcFlagsTableLabel := steinerUnaryArcTableMachine.ΛFin

private inductive GraphArcFlagsLabel where
  | prepare (label : ArcFlagsPrepLabel)
  | table (label : ArcFlagsTableLabel)
  deriving Fintype

private abbrev GraphArcFlagsRegister := ArcFlagsPrepRegister × ArcFlagsTableRegister
private abbrev GraphArcFlagsProgram :=
  StackMachineTag.Program (Fin 8) (Option Bool) GraphArcFlagsLabel GraphArcFlagsRegister

private def graphArcFlagsInitial : GraphArcFlagsRegister :=
  (steinerUnaryGraphQueryFrameMachine.initialState,steinerUnaryArcTableMachine.initialState)

private def graphArcFlagsPrepTag :
    StackMachineTag (Option Bool) (Option Bool) ArcFlagsPrepLabel GraphArcFlagsLabel
      ArcFlagsPrepRegister GraphArcFlagsRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (r,steinerUnaryArcTableMachine.initialState)
  readRegister := Prod.fst
  writeLabel := .prepare
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def graphArcFlagsTableTag :
    StackMachineTag (Option Bool) (Option Bool) ArcFlagsTableLabel GraphArcFlagsLabel
      ArcFlagsTableRegister GraphArcFlagsRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (steinerUnaryGraphQueryFrameMachine.initialState,r)
  readRegister := Prod.snd
  writeLabel := .table
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def graphArcFlagsReturn : GraphArcFlagsLabel := .table steinerUnaryArcTableMachine.main

private def graphArcFlagsPrepSlots : Fin 7 ↪ Fin 8 :=
  ⟨Fin.castSucc,Fin.castSucc_injective 7⟩

private def graphArcFlagsInner :
    GraphArcFlagsLabel → StackMachineTag.Program (Fin 7) (Option Bool) GraphArcFlagsLabel GraphArcFlagsRegister
  | .prepare label =>
    graphArcFlagsPrepTag.returningStatement graphArcFlagsReturn (steinerUnaryGraphQueryFrameMachine.m label)
  | .table _ => Turing.TM2.Stmt.halt

private def graphArcFlagsProgram : GraphArcFlagsLabel → GraphArcFlagsProgram
  | .prepare label => StackIndexEmbedding.statement graphArcFlagsPrepSlots (graphArcFlagsInner (.prepare label))
  | .table label => graphArcFlagsTableTag.statement (steinerUnaryArcTableMachine.m label)

/-- The preparation phase returns into the table phase with its exact
output frame already on the table phase's input stack. -/
abbrev steinerUnaryGraphArcFlagsMachine : FinTM2 where
  K := Fin 8
  k₀ := 5
  k₁ := 4
  Γ _ := Option Bool
  Λ := GraphArcFlagsLabel
  main := .prepare steinerUnaryGraphQueryFrameMachine.main
  σ := GraphArcFlagsRegister
  initialState := graphArcFlagsInitial
  m := graphArcFlagsProgram

private def graphArcFlagsCfg (label : Option GraphArcFlagsLabel) (work input : List (Option Bool)) :
    steinerUnaryGraphArcFlagsMachine.Cfg where
  l := label
  var := graphArcFlagsInitial
  stk := ![[],[],[],[],work,input,[],[]]

private noncomputable def graphArcFlagsPrepared (c : steinerUnaryGraphQueryFrameMachine.Cfg) :
    steinerUnaryGraphArcFlagsMachine.Cfg :=
  StackIndexEmbedding.configuration graphArcFlagsPrepSlots (fun _ => [])
    (graphArcFlagsPrepTag.returningConfiguration graphArcFlagsReturn c)

private theorem graphArcFlags_prepStep {c after : steinerUnaryGraphQueryFrameMachine.Cfg}
    (move : steinerUnaryGraphQueryFrameMachine.step c = some after) :
    steinerUnaryGraphArcFlagsMachine.step (graphArcFlagsPrepared c) = some (graphArcFlagsPrepared after) := by
  have tagged := graphArcFlagsPrepTag.step_embedded_return graphArcFlagsReturn
    (base := steinerUnaryGraphQueryFrameMachine.m) (host := graphArcFlagsInner) (fun _ => rfl) move
  have framed := StackIndexEmbedding.step_on graphArcFlagsPrepSlots (base := graphArcFlagsInner)
    (fun _ => []) (graphArcFlagsPrepTag.returningConfiguration graphArcFlagsReturn c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem graphArcFlags_prepTapes (c : steinerUnaryGraphQueryFrameMachine.Cfg) (work input : List (Option Bool))
    (tapes : c.stk = ![[],[],[],[],work,input,[]]) :
    (graphArcFlagsPrepared c).stk = ![[],[],[],[],work,input,[],[]] := by
  have image (i : Fin 7) : (graphArcFlagsPrepared c).stk (graphArcFlagsPrepSlots i) =
      (![[],[],[],[],work,input,[]] : Fin 7 → List (Option Bool)) i := by
    change StackIndexEmbedding.tapesAt graphArcFlagsPrepSlots (fun k => (c.stk k).map id) (fun _ => [])
      (graphArcFlagsPrepSlots i) = _
    rw [StackIndexEmbedding.tapesAt_image,List.map_id,tapes]
  have extra : (graphArcFlagsPrepared c).stk 7 = [] := by
    change StackIndexEmbedding.tapesAt graphArcFlagsPrepSlots (fun k => (c.stk k).map id) (fun _ => []) 7 = []
    exact StackIndexEmbedding.tapesAt_extra graphArcFlagsPrepSlots _ _ (by intro j; fin_cases j <;> decide)
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

private theorem graphArcFlags_prepInit (input : List (Option Bool)) :
    graphArcFlagsPrepared (initList steinerUnaryGraphQueryFrameMachine input) =
      initList steinerUnaryGraphArcFlagsMachine input := by
  have lifted := graphArcFlags_prepTapes (initList steinerUnaryGraphQueryFrameMachine input) [] input
    (by funext i; fin_cases i <;> rfl)
  apply congrArg (fun stk : Fin 8 → List (Option Bool) =>
    (⟨some (.prepare steinerUnaryGraphQueryFrameMachine.main),graphArcFlagsInitial,stk⟩ :
      steinerUnaryGraphArcFlagsMachine.Cfg))
  refine lifted.trans ?_
  funext i
  fin_cases i <;> rfl

private theorem graphArcFlags_prepReturn (work : List (Option Bool)) :
    graphArcFlagsPrepared (haltList steinerUnaryGraphQueryFrameMachine work) =
      graphArcFlagsCfg (some graphArcFlagsReturn) work [] := by
  apply congrArg (fun stk : Fin 8 → List (Option Bool) =>
    (⟨some graphArcFlagsReturn,graphArcFlagsInitial,stk⟩ : steinerUnaryGraphArcFlagsMachine.Cfg))
  apply graphArcFlags_prepTapes
  funext i
  fin_cases i <;> rfl

private theorem graphArcFlags_tableInit (work : List (Option Bool)) :
    graphArcFlagsTableTag.configuration (initList steinerUnaryArcTableMachine work) =
      graphArcFlagsCfg (some graphArcFlagsReturn) work [] := by
  apply congrArg (fun stk : Fin 8 → List (Option Bool) =>
    (⟨some graphArcFlagsReturn,graphArcFlagsInitial,stk⟩ : steinerUnaryGraphArcFlagsMachine.Cfg))
  funext i
  change ((initList steinerUnaryArcTableMachine work).stk i).map id =
    (graphArcFlagsCfg (some graphArcFlagsReturn) work []).stk i
  rw [List.map_id]
  fin_cases i <;> rfl

private theorem graphArcFlags_tableHalt (out : List (Option Bool)) :
    graphArcFlagsTableTag.configuration (haltList steinerUnaryArcTableMachine out) =
      haltList steinerUnaryGraphArcFlagsMachine out := by
  apply congrArg (fun stk : Fin 8 → List (Option Bool) =>
    (⟨none,graphArcFlagsInitial,stk⟩ : steinerUnaryGraphArcFlagsMachine.Cfg))
  funext i
  change ((haltList steinerUnaryArcTableMachine out).stk i).map id =
    (haltList steinerUnaryGraphArcFlagsMachine out).stk i
  rw [List.map_id]
  rfl

private def graphArcFlags_sequence {time : ℕ} (request : SteinerUnaryGraphQueryFrame) (out : List (Option Bool))
    (run : TM2OutputsInTime steinerUnaryArcTableMachine (steinerUnaryGraphQueryFrameAnswer request) (some out) time) :
    let X := (encodeSteinerUnaryGraphQueryFrame request).length
    TM2OutputsInTime steinerUnaryGraphArcFlagsMachine (encodeSteinerUnaryGraphQueryFrame request) (some out)
      (2*X^3+5*X^2+9*X+7+time) := by
  let prep := steinerUnaryGraphQueryFrameMachine_cubic request
  let X := (encodeSteinerUnaryGraphQueryFrame request).length
  let frame := steinerUnaryGraphQueryFrameAnswer request
  have executed := iterate_map_some graphArcFlagsPrepared (fun move => graphArcFlags_prepStep move)
    prep.steps prep.evals_in_steps
  change (flip bind steinerUnaryGraphArcFlagsMachine.step)^[prep.steps]
    (some (graphArcFlagsPrepared (initList steinerUnaryGraphQueryFrameMachine
      (encodeSteinerUnaryGraphQueryFrame request)))) =
    some (graphArcFlagsPrepared (haltList steinerUnaryGraphQueryFrameMachine frame)) at executed
  rw [graphArcFlags_prepInit,graphArcFlags_prepReturn] at executed
  have prepared : EvalsToInTime steinerUnaryGraphArcFlagsMachine.step
      (initList steinerUnaryGraphArcFlagsMachine (encodeSteinerUnaryGraphQueryFrame request))
      (some (graphArcFlagsCfg (some graphArcFlagsReturn) frame [])) (2*X^3+5*X^2+9*X+7) :=
    ⟨⟨prep.steps,executed⟩,prep.steps_le_m⟩
  have queried := graphArcFlagsTableTag.evaluation (base := steinerUnaryArcTableMachine.m)
    (host := graphArcFlagsProgram) (fun _ => rfl) run
  change EvalsToInTime steinerUnaryGraphArcFlagsMachine.step
    (graphArcFlagsTableTag.configuration (initList steinerUnaryArcTableMachine frame))
    (some (graphArcFlagsTableTag.configuration (haltList steinerUnaryArcTableMachine out))) time at queried
  rw [graphArcFlags_tableInit,graphArcFlags_tableHalt] at queried
  have all := EvalsToInTime.trans _ _ _ _ _ _ prepared queried
  refine ⟨all.toEvalsTo,?_⟩
  change all.steps ≤ 2*X^3+5*X^2+9*X+7+time
  exact all.steps_le_m.trans (by rw [Nat.add_comm time])

private theorem graphArcFlags_bound (request : SteinerUnaryGraphQueryFrame) :
    let X := (encodeSteinerUnaryGraphQueryFrame request).length
    let Y := (steinerUnaryGraphQueryFrameAnswer request).length
    let C := X^3+X^2+X
    (2*X^3+5*X^2+9*X+7)+(5*Y^2+14*Y+4) ≤ 5*C^2+14*C+2*X^3+5*X^2+9*X+11 := by
  dsimp only
  let X := (encodeSteinerUnaryGraphQueryFrame request).length
  let Y := (steinerUnaryGraphQueryFrameAnswer request).length
  let G := (encodeSteinerUnaryArcRows request.2).length
  have input : X = request.1+1+G := encodeSteinerUnaryGraphQueryFrame_length request
  have frame : Y = G+1+request.1^3+request.1^2 := steinerUnaryGraphQueryFrameAnswer_length request
  have bounded : request.1 ≤ X := by omega
  have cube := Nat.pow_le_pow_left bounded 3
  have square := Nat.pow_le_pow_left bounded 2
  have length : Y ≤ X^3+X^2+X := by omega
  have squared := Nat.pow_le_pow_left length 2
  change (2*X^3+5*X^2+9*X+7)+(5*Y^2+14*Y+4) ≤
    5*(X^3+X^2+X)^2+14*(X^3+X^2+X)+2*X^3+5*X^2+9*X+11
  omega

/-- One flag per ordered pair, in the order of the graph query enumeration. -/
def steinerUnaryGraphArcFlagsAnswer (request : SteinerUnaryGraphQueryFrame) : List (Option Bool) :=
  steinerUnaryArcTableAnswer (request.2,(steinerAllArcQueries request.1).map steinerUnaryArcValues)

/-- The ordered membership table is computed from the unary vertex
count and original graph rows. -/
def steinerUnaryGraphArcFlagsMachine_run (request : SteinerUnaryGraphQueryFrame) :
    let X := (encodeSteinerUnaryGraphQueryFrame request).length
    let C := X^3+X^2+X
    TM2OutputsInTime steinerUnaryGraphArcFlagsMachine (encodeSteinerUnaryGraphQueryFrame request)
      (some (steinerUnaryGraphArcFlagsAnswer request)) (5*C^2+14*C+2*X^3+5*X^2+9*X+11) := by
  let run := graphArcFlags_sequence request _
    (steinerUnaryArcTableMachine_quadratic (request.2,(steinerAllArcQueries request.1).map steinerUnaryArcValues))
  exact ⟨run.toEvalsTo,run.steps_le_m.trans (graphArcFlags_bound request)⟩

/-- Duplicate rows describe the same finite graph. Every directed pair,
including the diagonal, receives its exact arc membership bit. -/
def steinerUnaryGraphArcFlagsMachine_finset {n : ℕ} (rows : List (Fin n × Fin n)) :
    let request : SteinerUnaryGraphQueryFrame := (n,rows.map steinerUnaryArcValues)
    let X := (encodeSteinerUnaryGraphQueryFrame request).length
    let C := X^3+X^2+X
    TM2OutputsInTime steinerUnaryGraphArcFlagsMachine (encodeSteinerUnaryGraphQueryFrame request)
      (some ((steinerAllArcQueries n).map fun arc => some (decide (arc ∈ rows.toFinset))))
      (5*C^2+14*C+2*X^3+5*X^2+9*X+11) := by
  let request : SteinerUnaryGraphQueryFrame := (n,rows.map steinerUnaryArcValues)
  let run := graphArcFlags_sequence request _ (steinerUnaryArcTableMachine_finset rows (steinerAllArcQueries n))
  exact ⟨run.toEvalsTo,run.steps_le_m.trans (graphArcFlags_bound request)⟩

/-- Polynomial native time in the encoded unary graph frame. -/
noncomputable def steinerUnaryGraphArcFlagsMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryGraphQueryFrame id steinerUnaryGraphArcFlagsAnswer where
  tm := steinerUnaryGraphArcFlagsMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time :=
    let C : Polynomial ℕ := Polynomial.X^3+Polynomial.X^2+Polynomial.X
    Polynomial.C 5*C^2+Polynomial.C 14*C+Polynomial.C 2*Polynomial.X^3+
      Polynomial.C 5*Polynomial.X^2+Polynomial.C 9*Polynomial.X+Polynomial.C 11
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_C] using steinerUnaryGraphArcFlagsMachine_run request

/-- Each vertex pair occupies one position in the flag stream. -/
theorem steinerUnaryGraphArcFlagsAnswer_length (request : SteinerUnaryGraphQueryFrame) :
    (steinerUnaryGraphArcFlagsAnswer request).length = request.1*request.1 := by
  simp only [steinerUnaryGraphArcFlagsAnswer,steinerUnaryArcTableAnswer,List.length_map,steinerAllArcQueries_length]

end OnlineReachabilityPreservers
