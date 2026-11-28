import OnlineReachabilityPreservers.SteinerUnaryGraphQueryFrameMachine

/-! Count distinct finite arcs from a unary vertex count and graph frame. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing

private abbrev ArcGraphPrepLabel := steinerUnaryGraphQueryFrameMachine.Λ
private abbrev ArcGraphPrepRegister := steinerUnaryGraphQueryFrameMachine.σ
private abbrev ArcGraphCountLabel := steinerUnaryArcCountMachine.Λ
private abbrev ArcGraphCountRegister := steinerUnaryArcCountMachine.σ
private instance : Fintype ArcGraphPrepLabel := steinerUnaryGraphQueryFrameMachine.ΛFin
private instance : Fintype ArcGraphCountLabel := steinerUnaryArcCountMachine.ΛFin

private inductive GraphArcCountLabel where
  | prepare (label : ArcGraphPrepLabel)
  | count (label : ArcGraphCountLabel)
  deriving Fintype

private abbrev GraphArcCountRegister := ArcGraphPrepRegister × ArcGraphCountRegister
private abbrev GraphArcCountProgram :=
  StackMachineTag.Program (Fin 8) (Option Bool) GraphArcCountLabel GraphArcCountRegister

private def graphArcCountInitial : GraphArcCountRegister :=
  (steinerUnaryGraphQueryFrameMachine.initialState,steinerUnaryArcCountMachine.initialState)

private def graphArcCountPrepTag :
    StackMachineTag (Option Bool) (Option Bool) ArcGraphPrepLabel GraphArcCountLabel
      ArcGraphPrepRegister GraphArcCountRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (r,steinerUnaryArcCountMachine.initialState)
  readRegister := Prod.fst
  writeLabel := .prepare
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def graphArcCountCountTag :
    StackMachineTag (Option Bool) (Option Bool) ArcGraphCountLabel GraphArcCountLabel
      ArcGraphCountRegister GraphArcCountRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (steinerUnaryGraphQueryFrameMachine.initialState,r)
  readRegister := Prod.snd
  writeLabel := .count
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def graphArcCountReturn : GraphArcCountLabel := .count steinerUnaryArcCountMachine.main

private def graphArcCountPrepSlots : Fin 7 ↪ Fin 8 :=
  ⟨Fin.castSucc,Fin.castSucc_injective 7⟩

private def graphArcCountInner :
    GraphArcCountLabel → StackMachineTag.Program (Fin 7) (Option Bool) GraphArcCountLabel GraphArcCountRegister
  | .prepare label =>
    graphArcCountPrepTag.returningStatement graphArcCountReturn (steinerUnaryGraphQueryFrameMachine.m label)
  | .count _ => Turing.TM2.Stmt.halt

private def graphArcCountProgram : GraphArcCountLabel → GraphArcCountProgram
  | .prepare label => StackIndexEmbedding.statement graphArcCountPrepSlots (graphArcCountInner (.prepare label))
  | .count label => graphArcCountCountTag.statement (steinerUnaryArcCountMachine.m label)

/-- The preparation phase returns into the count phase with its exact
output frame already on the count phase's input stack. -/
abbrev steinerUnaryGraphArcCountMachine : FinTM2 where
  K := Fin 8
  k₀ := 5
  k₁ := 4
  Γ _ := Option Bool
  Λ := GraphArcCountLabel
  main := .prepare steinerUnaryGraphQueryFrameMachine.main
  σ := GraphArcCountRegister
  initialState := graphArcCountInitial
  m := graphArcCountProgram

private def graphArcCountCfg (label : Option GraphArcCountLabel) (work input : List (Option Bool)) :
    steinerUnaryGraphArcCountMachine.Cfg where
  l := label
  var := graphArcCountInitial
  stk := ![[],[],[],[],work,input,[],[]]

private noncomputable def graphArcCountPrepared (c : steinerUnaryGraphQueryFrameMachine.Cfg) :
    steinerUnaryGraphArcCountMachine.Cfg :=
  StackIndexEmbedding.configuration graphArcCountPrepSlots (fun _ => [])
    (graphArcCountPrepTag.returningConfiguration graphArcCountReturn c)

private theorem graphArcCount_prepStep {c after : steinerUnaryGraphQueryFrameMachine.Cfg}
    (move : steinerUnaryGraphQueryFrameMachine.step c = some after) :
    steinerUnaryGraphArcCountMachine.step (graphArcCountPrepared c) = some (graphArcCountPrepared after) := by
  have tagged := graphArcCountPrepTag.step_embedded_return graphArcCountReturn
    (base := steinerUnaryGraphQueryFrameMachine.m) (host := graphArcCountInner) (fun _ => rfl) move
  have framed := StackIndexEmbedding.step_on graphArcCountPrepSlots (base := graphArcCountInner)
    (fun _ => []) (graphArcCountPrepTag.returningConfiguration graphArcCountReturn c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem graphArcCount_prepTapes (c : steinerUnaryGraphQueryFrameMachine.Cfg) (work input : List (Option Bool))
    (tapes : c.stk = ![[],[],[],[],work,input,[]]) :
    (graphArcCountPrepared c).stk = ![[],[],[],[],work,input,[],[]] := by
  have image (i : Fin 7) : (graphArcCountPrepared c).stk (graphArcCountPrepSlots i) =
      (![[],[],[],[],work,input,[]] : Fin 7 → List (Option Bool)) i := by
    change StackIndexEmbedding.tapesAt graphArcCountPrepSlots (fun k => (c.stk k).map id) (fun _ => [])
      (graphArcCountPrepSlots i) = _
    rw [StackIndexEmbedding.tapesAt_image,List.map_id,tapes]
  have extra : (graphArcCountPrepared c).stk 7 = [] := by
    change StackIndexEmbedding.tapesAt graphArcCountPrepSlots (fun k => (c.stk k).map id) (fun _ => []) 7 = []
    exact StackIndexEmbedding.tapesAt_extra graphArcCountPrepSlots _ _ (by intro j; fin_cases j <;> decide)
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

private theorem graphArcCount_prepInit (input : List (Option Bool)) :
    graphArcCountPrepared (initList steinerUnaryGraphQueryFrameMachine input) =
      initList steinerUnaryGraphArcCountMachine input := by
  have lifted := graphArcCount_prepTapes (initList steinerUnaryGraphQueryFrameMachine input) [] input
    (by funext i; fin_cases i <;> rfl)
  apply congrArg (fun stk : Fin 8 → List (Option Bool) =>
    (⟨some (.prepare steinerUnaryGraphQueryFrameMachine.main),graphArcCountInitial,stk⟩ :
      steinerUnaryGraphArcCountMachine.Cfg))
  refine lifted.trans ?_
  funext i
  fin_cases i <;> rfl

private theorem graphArcCount_prepReturn (work : List (Option Bool)) :
    graphArcCountPrepared (haltList steinerUnaryGraphQueryFrameMachine work) =
      graphArcCountCfg (some graphArcCountReturn) work [] := by
  apply congrArg (fun stk : Fin 8 → List (Option Bool) =>
    (⟨some graphArcCountReturn,graphArcCountInitial,stk⟩ : steinerUnaryGraphArcCountMachine.Cfg))
  apply graphArcCount_prepTapes
  funext i
  fin_cases i <;> rfl

private theorem graphArcCount_countInit (work : List (Option Bool)) :
    graphArcCountCountTag.configuration (initList steinerUnaryArcCountMachine work) =
      graphArcCountCfg (some graphArcCountReturn) work [] := by
  apply congrArg (fun stk : Fin 8 → List (Option Bool) =>
    (⟨some graphArcCountReturn,graphArcCountInitial,stk⟩ : steinerUnaryGraphArcCountMachine.Cfg))
  funext i
  change ((initList steinerUnaryArcCountMachine work).stk i).map id =
    (graphArcCountCfg (some graphArcCountReturn) work []).stk i
  rw [List.map_id]
  fin_cases i <;> rfl

private theorem graphArcCount_countHalt (out : List (Option Bool)) :
    graphArcCountCountTag.configuration (haltList steinerUnaryArcCountMachine out) =
      haltList steinerUnaryGraphArcCountMachine out := by
  apply congrArg (fun stk : Fin 8 → List (Option Bool) =>
    (⟨none,graphArcCountInitial,stk⟩ : steinerUnaryGraphArcCountMachine.Cfg))
  funext i
  change ((haltList steinerUnaryArcCountMachine out).stk i).map id =
    (haltList steinerUnaryGraphArcCountMachine out).stk i
  rw [List.map_id]
  rfl

private def graphArcCount_sequence {time : ℕ} (request : SteinerUnaryGraphQueryFrame) (out : List (Option Bool))
    (run : TM2OutputsInTime steinerUnaryArcCountMachine (steinerUnaryGraphQueryFrameAnswer request) (some out) time) :
    let X := (encodeSteinerUnaryGraphQueryFrame request).length
    TM2OutputsInTime steinerUnaryGraphArcCountMachine (encodeSteinerUnaryGraphQueryFrame request) (some out)
      (2*X^3+5*X^2+9*X+7+time) := by
  let prep := steinerUnaryGraphQueryFrameMachine_cubic request
  let X := (encodeSteinerUnaryGraphQueryFrame request).length
  let frame := steinerUnaryGraphQueryFrameAnswer request
  have executed := iterate_map_some graphArcCountPrepared (fun move => graphArcCount_prepStep move)
    prep.steps prep.evals_in_steps
  change (flip bind steinerUnaryGraphArcCountMachine.step)^[prep.steps]
    (some (graphArcCountPrepared (initList steinerUnaryGraphQueryFrameMachine
      (encodeSteinerUnaryGraphQueryFrame request)))) =
    some (graphArcCountPrepared (haltList steinerUnaryGraphQueryFrameMachine frame)) at executed
  rw [graphArcCount_prepInit,graphArcCount_prepReturn] at executed
  have prepared : EvalsToInTime steinerUnaryGraphArcCountMachine.step
      (initList steinerUnaryGraphArcCountMachine (encodeSteinerUnaryGraphQueryFrame request))
      (some (graphArcCountCfg (some graphArcCountReturn) frame [])) (2*X^3+5*X^2+9*X+7) :=
    ⟨⟨prep.steps,executed⟩,prep.steps_le_m⟩
  have counted := graphArcCountCountTag.evaluation (base := steinerUnaryArcCountMachine.m)
    (host := graphArcCountProgram) (fun _ => rfl) run
  change EvalsToInTime steinerUnaryGraphArcCountMachine.step
    (graphArcCountCountTag.configuration (initList steinerUnaryArcCountMachine frame))
    (some (graphArcCountCountTag.configuration (haltList steinerUnaryArcCountMachine out))) time at counted
  rw [graphArcCount_countInit,graphArcCount_countHalt] at counted
  have all := EvalsToInTime.trans _ _ _ _ _ _ prepared counted
  refine ⟨all.toEvalsTo,?_⟩
  change all.steps ≤ 2*X^3+5*X^2+9*X+7+time
  exact all.steps_le_m.trans (by rw [Nat.add_comm time])

private theorem graphArcCount_bound (request : SteinerUnaryGraphQueryFrame) :
    let X := (encodeSteinerUnaryGraphQueryFrame request).length
    let Y := (steinerUnaryGraphQueryFrameAnswer request).length
    let C := X^3+X^2+X
    (2*X^3+5*X^2+9*X+7)+(5*Y^2+16*Y+6) ≤ 5*C^2+16*C+2*X^3+5*X^2+9*X+13 := by
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
  change (2*X^3+5*X^2+9*X+7)+(5*Y^2+16*Y+6) ≤
    5*(X^3+X^2+X)^2+16*(X^3+X^2+X)+2*X^3+5*X^2+9*X+13
  omega

/-- The unary tally for the arcs present among the candidates generated
from the vertex count. -/
def steinerUnaryGraphArcCountAnswer (request : SteinerUnaryGraphQueryFrame) : List (Option Bool) :=
  steinerUnaryArcCountAnswer (request.2,(steinerAllArcQueries request.1).map steinerUnaryArcValues)

/-- Run both phases from the supplied unary vertex count and graph. -/
def steinerUnaryGraphArcCountMachine_run (request : SteinerUnaryGraphQueryFrame) :
    let X := (encodeSteinerUnaryGraphQueryFrame request).length
    let C := X^3+X^2+X
    TM2OutputsInTime steinerUnaryGraphArcCountMachine (encodeSteinerUnaryGraphQueryFrame request)
      (some (steinerUnaryGraphArcCountAnswer request)) (5*C^2+16*C+2*X^3+5*X^2+9*X+13) := by
  let run := graphArcCount_sequence request _
    (steinerUnaryArcCountMachine_quadratic (request.2,(steinerAllArcQueries request.1).map steinerUnaryArcValues))
  exact ⟨run.toEvalsTo,run.steps_le_m.trans (graphArcCount_bound request)⟩

/-- Count the distinct arcs of any finite graph given its unary vertex
count and ordered unary rows, including repeated rows and loops. -/
def steinerUnaryGraphArcCountMachine_finset {n : ℕ} (rows : List (Fin n × Fin n)) :
    let request : SteinerUnaryGraphQueryFrame := (n,rows.map steinerUnaryArcValues)
    let X := (encodeSteinerUnaryGraphQueryFrame request).length
    let C := X^3+X^2+X
    TM2OutputsInTime steinerUnaryGraphArcCountMachine (encodeSteinerUnaryGraphQueryFrame request)
      (some (List.replicate rows.toFinset.card (some true))) (5*C^2+16*C+2*X^3+5*X^2+9*X+13) := by
  let request : SteinerUnaryGraphQueryFrame := (n,rows.map steinerUnaryArcValues)
  let run := graphArcCount_sequence request _ (steinerUnaryArcCountMachine_all_pairs rows)
  exact ⟨run.toEvalsTo,run.steps_le_m.trans (graphArcCount_bound request)⟩

/-- An actual polynomial transition bound in the unary graph input length. -/
noncomputable def steinerUnaryGraphArcCountMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryGraphQueryFrame id steinerUnaryGraphArcCountAnswer where
  tm := steinerUnaryGraphArcCountMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time :=
    let C : Polynomial ℕ := Polynomial.X^3+Polynomial.X^2+Polynomial.X
    Polynomial.C 5*C^2+Polynomial.C 16*C+Polynomial.C 2*Polynomial.X^3+
      Polynomial.C 5*Polynomial.X^2+Polynomial.C 9*Polynomial.X+Polynomial.C 13
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,
      Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_pow] using steinerUnaryGraphArcCountMachine_run request

end OnlineReachabilityPreservers
