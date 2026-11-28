import OnlineReachabilityPreservers.SteinerSeedDecoderWork
import OnlineReachabilityPreservers.SteinerStackFrame
import OnlineReachabilityPreservers.SteinerStackReturn
import OnlineReachabilityPreservers.SteinerUnaryProductMachine

/-! Compute a unary scaled sum of products, including the seed budget
arithmetic on prepared decoder dimensions. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev ProductLabel := steinerUnaryProductMachine.Λ
private instance : Fintype ProductLabel := steinerUnaryProductMachine.ΛFin

private inductive ScaledProductLabel where
  | collectFactor
  | subtotal (label : ProductLabel)
  | buildTail
  | moveSubtotal
  | moveFactor
  | multiply (label : ProductLabel)
  deriving Fintype

private abbrev ScaledProductRegister := steinerUnaryProductMachine.σ
private abbrev ScaledProductProgram := StackMachineTag.Program (Fin 6) Bool ScaledProductLabel ScaledProductRegister

private def scaledProductTag (label : ProductLabel → ScaledProductLabel) :
    StackMachineTag Bool Bool ProductLabel ScaledProductLabel ScaledProductRegister ScaledProductRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister := id
  readRegister := id
  writeLabel := label
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def scaledProductSlots : Fin 5 ↪ Fin 6 :=
  ⟨Fin.castSucc,Fin.castSucc_injective _⟩

private def scaledProductInner :
    ScaledProductLabel → StackMachineTag.Program (Fin 5) Bool ScaledProductLabel ScaledProductRegister
  | .subtotal label =>
    (scaledProductTag .subtotal).returningStatement .buildTail (steinerUnaryProductMachine.m label)
  | .multiply label => (scaledProductTag .multiply).statement (steinerUnaryProductMachine.m label)
  | _ => halt

private def scaledProductObserve (_ : ScaledProductRegister) (seen : Option Bool) : ScaledProductRegister := seen

private def scaledProductNext (label : ScaledProductLabel) : ScaledProductProgram :=
  load (fun _ => none) (goto (fun _ => label))

private def scaledProductProgram : ScaledProductLabel → ScaledProductProgram
  | .collectFactor =>
    pop 0 scaledProductObserve <|
      branch (·.getD false)
        (push 5 (fun _ => true) (scaledProductNext .collectFactor))
        (scaledProductNext (.subtotal steinerUnaryProductMachine.main))
  | .subtotal label => StackIndexEmbedding.statement scaledProductSlots (scaledProductInner (.subtotal label))
  | .buildTail => push 0 (fun _ => false) (scaledProductNext .moveSubtotal)
  | .moveSubtotal =>
    pop 4 scaledProductObserve <|
      branch Option.isSome
        (push 0 (fun _ => true) (scaledProductNext .moveSubtotal))
        (push 0 (fun _ => false) (scaledProductNext .moveFactor))
  | .moveFactor =>
    pop 5 scaledProductObserve <|
      branch Option.isSome
        (push 0 (fun _ => true) (scaledProductNext .moveFactor))
        (scaledProductNext (.multiply steinerUnaryProductMachine.main))
  | .multiply label => StackIndexEmbedding.statement scaledProductSlots (scaledProductInner (.multiply label))

/-- Preserve the leading factor while the first invocation sums the
products. Frame the factor and the subtotal for a second invocation
that returns their product. -/
abbrev steinerScaledProductMachine : FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := ScaledProductLabel
  main := .collectFactor
  σ := ScaledProductRegister
  initialState := none
  m := scaledProductProgram

private abbrev tallies (n : ℕ) := encodeSteinerUnaryProductCount n

private def scaledProductCfg (label : Option ScaledProductLabel) (input : List Bool) (out factor : ℕ) :
    steinerScaledProductMachine.Cfg where
  l := label
  var := none
  stk := ![input,[],[],[],tallies out,tallies factor]

private theorem scaledProduct_update0 (input out factor word : List Bool) :
    Function.update (![input,[],[],[],out,factor] : Fin 6 → List Bool) 0 word = ![word,[],[],[],out,factor] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem scaledProduct_update4 (input out factor word : List Bool) :
    Function.update (![input,[],[],[],out,factor] : Fin 6 → List Bool) 4 word = ![input,[],[],[],word,factor] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem scaledProduct_update5 (input out factor word : List Bool) :
    Function.update (![input,[],[],[],out,factor] : Fin 6 → List Bool) 5 word = ![input,[],[],[],out,word] := by
  funext i
  fin_cases i <;> simp [Function.update]

private abbrev ScaledProductRun (start finish : steinerScaledProductMachine.Cfg) (steps : ℕ) : Prop :=
  (flip bind steinerScaledProductMachine.step)^[steps] (some start) = some finish

private theorem scaledProduct_one {start finish : steinerScaledProductMachine.Cfg}
    (move : steinerScaledProductMachine.step start = some finish) : ScaledProductRun start finish 1 := move

private theorem scaledProduct_join {start between finish : steinerScaledProductMachine.Cfg} {a b : ℕ}
    (first : ScaledProductRun start between a) (second : ScaledProductRun between finish b) :
    ScaledProductRun start finish (a+b) := by
  unfold ScaledProductRun at *
  rw [Nat.add_comm a b,Function.iterate_add_apply,first]
  exact second

private theorem scaledProduct_collectTally (rest : List Bool) (factor : ℕ) :
    ScaledProductRun (scaledProductCfg (some .collectFactor) (true::rest) 0 factor)
      (scaledProductCfg (some .collectFactor) rest 0 (factor+1)) 1 := by
  apply scaledProduct_one
  simp [FinTM2.step,steinerScaledProductMachine,scaledProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    scaledProductProgram,scaledProductObserve,scaledProductNext,scaledProduct_update0,scaledProduct_update5,
    encodeSteinerUnaryProductCount,List.replicate_succ]
  rfl

private theorem scaledProduct_collectEnd (rest : List Bool) (factor : ℕ) :
    ScaledProductRun (scaledProductCfg (some .collectFactor) (false::rest) 0 factor)
      (scaledProductCfg (some (.subtotal steinerUnaryProductMachine.main)) rest 0 factor) 1 := by
  apply scaledProduct_one
  simp [FinTM2.step,steinerScaledProductMachine,scaledProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    scaledProductProgram,scaledProductObserve,scaledProductNext,scaledProduct_update0]
  rfl

private theorem scaledProduct_tally_succ (x : ℕ) : tallies (x+1) = true::tallies x :=
  List.replicate_succ

private theorem scaledProduct_collect (rest : List Bool) (remaining factor : ℕ) :
    ScaledProductRun (scaledProductCfg (some .collectFactor) (tallies remaining++false::rest) 0 factor)
      (scaledProductCfg (some (.subtotal steinerUnaryProductMachine.main)) rest 0 (factor+remaining)) (remaining+1) := by
  induction remaining generalizing factor with
  | zero =>
    simpa only [encodeSteinerUnaryProductCount,List.replicate_zero,List.nil_append,Nat.add_zero,Nat.zero_add]
      using scaledProduct_collectEnd rest factor
  | succ remaining ih =>
    have all := scaledProduct_join (scaledProduct_collectTally (tallies remaining++false::rest) factor) (ih (factor+1))
    have count : factor+1+remaining = factor+(remaining+1) := by omega
    have paid : 1+(remaining+1) = remaining+1+1 := by omega
    simpa only [scaledProduct_tally_succ,List.cons_append,count,paid] using all

private theorem scaledProduct_buildTail (out factor : ℕ) :
    ScaledProductRun (scaledProductCfg (some .buildTail) [] out factor)
      (scaledProductCfg (some .moveSubtotal) [false] out factor) 1 := by
  apply scaledProduct_one
  simp [FinTM2.step,steinerScaledProductMachine,scaledProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    scaledProductProgram,scaledProductNext,scaledProduct_update0]
  rfl

private theorem scaledProduct_moveSubtotalTally (input : List Bool) (out factor : ℕ) :
    ScaledProductRun (scaledProductCfg (some .moveSubtotal) input (out+1) factor)
      (scaledProductCfg (some .moveSubtotal) (true::input) out factor) 1 := by
  apply scaledProduct_one
  simp [FinTM2.step,steinerScaledProductMachine,scaledProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    scaledProductProgram,scaledProductObserve,scaledProductNext,scaledProduct_update0,scaledProduct_update4,
    encodeSteinerUnaryProductCount,List.replicate_succ]
  rfl

private theorem scaledProduct_moveSubtotalEnd (input : List Bool) (factor : ℕ) :
    ScaledProductRun (scaledProductCfg (some .moveSubtotal) input 0 factor)
      (scaledProductCfg (some .moveFactor) (false::input) 0 factor) 1 := by
  apply scaledProduct_one
  simp [FinTM2.step,steinerScaledProductMachine,scaledProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    scaledProductProgram,scaledProductObserve,scaledProductNext,scaledProduct_update0,scaledProduct_update4,
    encodeSteinerUnaryProductCount]
  rfl

private theorem scaledProduct_moveFactorTally (input : List Bool) (factor : ℕ) :
    ScaledProductRun (scaledProductCfg (some .moveFactor) input 0 (factor+1))
      (scaledProductCfg (some .moveFactor) (true::input) 0 factor) 1 := by
  apply scaledProduct_one
  simp [FinTM2.step,steinerScaledProductMachine,scaledProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    scaledProductProgram,scaledProductObserve,scaledProductNext,scaledProduct_update0,scaledProduct_update5,
    encodeSteinerUnaryProductCount,List.replicate_succ]
  rfl

private theorem scaledProduct_moveFactorEnd (input : List Bool) :
    ScaledProductRun (scaledProductCfg (some .moveFactor) input 0 0)
      (scaledProductCfg (some (.multiply steinerUnaryProductMachine.main)) input 0 0) 1 := by
  apply scaledProduct_one
  simp [FinTM2.step,steinerScaledProductMachine,scaledProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    scaledProductProgram,scaledProductObserve,scaledProductNext,scaledProduct_update5,encodeSteinerUnaryProductCount]
  rfl

private theorem scaledProduct_moveSubtotal (input : List Bool) (out factor : ℕ) :
    ScaledProductRun (scaledProductCfg (some .moveSubtotal) input out factor)
      (scaledProductCfg (some .moveFactor) (false::(tallies out++input)) 0 factor) (out+1) := by
  induction out generalizing input with
  | zero =>
    simpa only [encodeSteinerUnaryProductCount,List.replicate_zero,List.nil_append,Nat.zero_add]
      using scaledProduct_moveSubtotalEnd input factor
  | succ out ih =>
    have all := scaledProduct_join (scaledProduct_moveSubtotalTally input out factor) (ih (true::input))
    have word : tallies out++true::input = tallies (out+1)++input := by
      simp [encodeSteinerUnaryProductCount,List.replicate_succ',List.append_assoc]
    have paid : 1+(out+1) = out+1+1 := by omega
    simpa only [word,paid] using all

private theorem scaledProduct_moveFactor (input : List Bool) (factor : ℕ) :
    ScaledProductRun (scaledProductCfg (some .moveFactor) input 0 factor)
      (scaledProductCfg (some (.multiply steinerUnaryProductMachine.main)) (tallies factor++input) 0 0) (factor+1) := by
  induction factor generalizing input with
  | zero =>
    simpa only [encodeSteinerUnaryProductCount,List.replicate_zero,List.nil_append,Nat.zero_add]
      using scaledProduct_moveFactorEnd input
  | succ factor ih =>
    have all := scaledProduct_join (scaledProduct_moveFactorTally input factor) (ih (true::input))
    have word : tallies factor++true::input = tallies (factor+1)++input := by
      simp [encodeSteinerUnaryProductCount,List.replicate_succ',List.append_assoc]
    have paid : 1+(factor+1) = factor+1+1 := by omega
    simpa only [word,paid] using all

private def scaledProductPassive (factor : ℕ) (i : Fin 6) : List Bool :=
  if i = 5 then tallies factor else []

private theorem scaledProduct_excludes_factor (i : Fin 5) : scaledProductSlots i ≠ 5 := by
  fin_cases i <;> decide

private theorem scaledProduct_tapes (input : List Bool) (out factor : ℕ) :
    StackIndexEmbedding.tapesAt scaledProductSlots (![input,[],[],[],tallies out] : Fin 5 → List Bool)
        (scaledProductPassive factor) =
      ![input,[],[],[],tallies out,tallies factor] := by
  have image (i : Fin 5) := StackIndexEmbedding.tapesAt_image scaledProductSlots
    (![input,[],[],[],tallies out] : Fin 5 → List Bool) (scaledProductPassive factor) i
  funext i
  fin_cases i
  · exact image 0
  · exact image 1
  · exact image 2
  · exact image 3
  · exact image 4
  · change StackIndexEmbedding.tapesAt scaledProductSlots _ (scaledProductPassive factor) 5 = _
    rw [StackIndexEmbedding.tapesAt_extra _ _ _ scaledProduct_excludes_factor,scaledProductPassive,ite_eq_left rfl]
    rfl

private theorem scaledProduct_sourceInit (input : List Bool) :
    (initList steinerUnaryProductMachine input).stk = ![input,[],[],[],tallies 0] := by
  funext i
  fin_cases i <;> rfl

private theorem scaledProduct_sourceHalt (out : ℕ) :
    (haltList steinerUnaryProductMachine (tallies out)).stk = ![[],[],[],[],tallies out] := by
  funext i
  fin_cases i <;> rfl

private noncomputable def scaledSubtotalCfg (factor : ℕ) (c : steinerUnaryProductMachine.Cfg) :
    steinerScaledProductMachine.Cfg :=
  StackIndexEmbedding.configuration scaledProductSlots (scaledProductPassive factor)
    ((scaledProductTag .subtotal).returningConfiguration .buildTail c)

private theorem scaledProduct_subtotalStep (factor : ℕ) {c after : steinerUnaryProductMachine.Cfg}
    (move : steinerUnaryProductMachine.step c = some after) :
    steinerScaledProductMachine.step (scaledSubtotalCfg factor c) = some (scaledSubtotalCfg factor after) := by
  have tagged := (scaledProductTag .subtotal).step_embedded_return .buildTail
    (base := steinerUnaryProductMachine.m) (host := scaledProductInner) (fun _ => rfl) move
  have framed := StackIndexEmbedding.step_on scaledProductSlots (base := scaledProductInner)
    (scaledProductPassive factor) ((scaledProductTag .subtotal).returningConfiguration .buildTail c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem scaledProduct_subtotalInit (input : List Bool) (factor : ℕ) :
    scaledSubtotalCfg factor (initList steinerUnaryProductMachine input) =
      scaledProductCfg (some (.subtotal steinerUnaryProductMachine.main)) input 0 factor := by
  apply congrArg (fun stk : Fin 6 → List Bool =>
    (⟨some (.subtotal steinerUnaryProductMachine.main),none,stk⟩ : steinerScaledProductMachine.Cfg))
  change StackIndexEmbedding.tapesAt scaledProductSlots (fun i => ((initList steinerUnaryProductMachine input).stk i).map id)
    (scaledProductPassive factor) = _
  simp only [List.map_id_fun,scaledProduct_sourceInit]
  exact scaledProduct_tapes input 0 factor

private theorem scaledProduct_subtotalReturn (out factor : ℕ) :
    scaledSubtotalCfg factor (haltList steinerUnaryProductMachine (tallies out)) =
      scaledProductCfg (some .buildTail) [] out factor := by
  apply congrArg (fun stk : Fin 6 → List Bool =>
    (⟨some .buildTail,none,stk⟩ : steinerScaledProductMachine.Cfg))
  change StackIndexEmbedding.tapesAt scaledProductSlots (fun i => ((haltList steinerUnaryProductMachine (tallies out)).stk i).map id)
    (scaledProductPassive factor) = _
  simp only [List.map_id_fun,scaledProduct_sourceHalt]
  exact scaledProduct_tapes [] out factor

private theorem scaledProduct_subtotal (requests : List (ℕ × ℕ)) (factor : ℕ) :
    ScaledProductRun (scaledProductCfg (some (.subtotal steinerUnaryProductMachine.main))
      (encodeSteinerUnaryProductRequests requests) 0 factor)
      (scaledProductCfg (some .buildTail) [] (steinerUnaryProductSum requests) factor)
      (steinerUnaryProductSteps requests) := by
  let run := steinerUnaryProductMachine_run requests
  have evaluated := iterate_map_some (scaledSubtotalCfg factor) (fun move => scaledProduct_subtotalStep factor move)
    run.steps run.evals_in_steps
  change ScaledProductRun (scaledSubtotalCfg factor (initList steinerUnaryProductMachine (encodeSteinerUnaryProductRequests requests)))
    (scaledSubtotalCfg factor (haltList steinerUnaryProductMachine (tallies (steinerUnaryProductSum requests))))
    (steinerUnaryProductSteps requests) at evaluated
  rw [scaledProduct_subtotalInit,scaledProduct_subtotalReturn] at evaluated
  exact evaluated

private theorem scaledProduct_frame (out factor : ℕ) :
    ScaledProductRun (scaledProductCfg (some .buildTail) [] out factor)
      (scaledProductCfg (some (.multiply steinerUnaryProductMachine.main))
        (encodeSteinerUnaryProductRequests [(factor,out)]) 0 0) (out+factor+3) := by
  have tail := scaledProduct_buildTail out factor
  have moved := scaledProduct_moveSubtotal [false] out factor
  have last := scaledProduct_moveFactor (false::(tallies out++[false])) factor
  have all := scaledProduct_join (scaledProduct_join tail moved) last
  have count : 1+(out+1)+(factor+1) = out+factor+3 := by omega
  have word : encodeSteinerUnaryProductRequests [(factor,out)] = tallies factor++false::(tallies out++[false]) := by
    simp only [encodeSteinerUnaryProductRequests,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rfl
  rw [word,← count]
  exact all

private noncomputable def scaledMultiplyCfg (c : steinerUnaryProductMachine.Cfg) :
    steinerScaledProductMachine.Cfg :=
  StackIndexEmbedding.configuration scaledProductSlots (scaledProductPassive 0)
    ((scaledProductTag .multiply).configuration c)

private theorem scaledProduct_multiplyStep {c after : steinerUnaryProductMachine.Cfg}
    (move : steinerUnaryProductMachine.step c = some after) :
    steinerScaledProductMachine.step (scaledMultiplyCfg c) = some (scaledMultiplyCfg after) := by
  have tagged := (scaledProductTag .multiply).step_embedded (base := steinerUnaryProductMachine.m)
    (host := scaledProductInner) (fun _ => rfl) c
  change Turing.TM2.step scaledProductInner ((scaledProductTag .multiply).configuration c) =
    (steinerUnaryProductMachine.step c).map (scaledProductTag .multiply).configuration at tagged
  rw [move] at tagged
  change Turing.TM2.step scaledProductInner ((scaledProductTag .multiply).configuration c) =
    some ((scaledProductTag .multiply).configuration after) at tagged
  have framed := StackIndexEmbedding.step_on scaledProductSlots (base := scaledProductInner)
    (scaledProductPassive 0) ((scaledProductTag .multiply).configuration c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem scaledProduct_multiplyInit (input : List Bool) :
    scaledMultiplyCfg (initList steinerUnaryProductMachine input) =
      scaledProductCfg (some (.multiply steinerUnaryProductMachine.main)) input 0 0 := by
  apply congrArg (fun stk : Fin 6 → List Bool =>
    (⟨some (.multiply steinerUnaryProductMachine.main),none,stk⟩ : steinerScaledProductMachine.Cfg))
  change StackIndexEmbedding.tapesAt scaledProductSlots (fun i => ((initList steinerUnaryProductMachine input).stk i).map id)
    (scaledProductPassive 0) = _
  simp only [List.map_id_fun,scaledProduct_sourceInit]
  exact scaledProduct_tapes input 0 0

private theorem scaledProduct_multiplyHalt (out : ℕ) :
    scaledMultiplyCfg (haltList steinerUnaryProductMachine (tallies out)) =
      scaledProductCfg none [] out 0 := by
  apply congrArg (fun stk : Fin 6 → List Bool => (⟨none,none,stk⟩ : steinerScaledProductMachine.Cfg))
  change StackIndexEmbedding.tapesAt scaledProductSlots (fun i => ((haltList steinerUnaryProductMachine (tallies out)).stk i).map id)
    (scaledProductPassive 0) = _
  simp only [List.map_id_fun,scaledProduct_sourceHalt]
  exact scaledProduct_tapes [] out 0

private theorem scaledProduct_multiply (out factor : ℕ) :
    ScaledProductRun (scaledProductCfg (some (.multiply steinerUnaryProductMachine.main))
        (encodeSteinerUnaryProductRequests [(factor,out)]) 0 0)
      (scaledProductCfg none [] (out*factor) 0) (steinerUnaryProductPairSteps (factor,out)+1) := by
  let run := steinerUnaryProductMachine_run [(factor,out)]
  have evaluated := iterate_map_some scaledMultiplyCfg (fun move => scaledProduct_multiplyStep move)
    run.steps run.evals_in_steps
  change ScaledProductRun (scaledMultiplyCfg (initList steinerUnaryProductMachine (encodeSteinerUnaryProductRequests [(factor,out)])))
    (scaledMultiplyCfg (haltList steinerUnaryProductMachine (tallies (steinerUnaryProductSum [(factor,out)]))))
    (steinerUnaryProductSteps [(factor,out)]) at evaluated
  rw [scaledProduct_multiplyInit,scaledProduct_multiplyHalt] at evaluated
  simpa [steinerUnaryProductSum,steinerUnaryProductSteps,Nat.mul_comm factor out] using evaluated

private theorem scaledProduct_init (input : List Bool) :
    initList steinerScaledProductMachine input = scaledProductCfg (some .collectFactor) input 0 0 := by
  apply congrArg (fun stk : Fin 6 → List Bool => (⟨some .collectFactor,none,stk⟩ : steinerScaledProductMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem scaledProduct_halt (out : ℕ) :
    haltList steinerScaledProductMachine (tallies out) = scaledProductCfg none [] out 0 := by
  apply congrArg (fun stk : Fin 6 → List Bool => (⟨none,none,stk⟩ : steinerScaledProductMachine.Cfg))
  funext i
  fin_cases i <;> rfl

abbrev SteinerScaledProductRequest := ℕ × List (ℕ × ℕ)

/-- The unary factor and its delimiter precede the framed operand pairs. -/
def encodeSteinerScaledProductRequest (request : SteinerScaledProductRequest) : List Bool :=
  tallies request.1 ++ false::encodeSteinerUnaryProductRequests request.2

/-- Multiply the subtotal of pair products by the leading factor. -/
def steinerScaledProduct (request : SteinerScaledProductRequest) : ℕ :=
  steinerUnaryProductSum request.2*request.1

/-- Count the two subroutine evaluations and the transitions used to
collect the factor and build the intermediate frame. -/
def steinerScaledProductSteps (request : SteinerScaledProductRequest) : ℕ :=
  let factor := request.1
  let out := steinerUnaryProductSum request.2
  steinerUnaryProductSteps request.2+2*factor*out+6*factor+3*out+9

/-- The composed machine returns the exact unary scaled sum. -/
def steinerScaledProductMachine_run (request : SteinerScaledProductRequest) :
    TM2OutputsInTime steinerScaledProductMachine (encodeSteinerScaledProductRequest request)
      (some (encodeSteinerUnaryProductCount (steinerScaledProduct request))) (steinerScaledProductSteps request) where
  steps := steinerScaledProductSteps request
  steps_le_m := le_rfl
  evals_in_steps := by
    rcases request with ⟨factor,requests⟩
    let out := steinerUnaryProductSum requests
    have first := scaledProduct_collect (encodeSteinerUnaryProductRequests requests) factor 0
    rw [Nat.zero_add] at first
    have summed := scaledProduct_join first (scaledProduct_subtotal requests factor)
    have framed := scaledProduct_join summed (scaledProduct_frame out factor)
    have all := scaledProduct_join framed (scaledProduct_multiply out factor)
    have paid : factor+1+steinerUnaryProductSteps requests+(out+factor+3)+
        (steinerUnaryProductPairSteps (factor,out)+1) = steinerScaledProductSteps (factor,requests) := by
      unfold steinerUnaryProductPairSteps steinerScaledProductSteps
      dsimp [out]
      ring
    change ScaledProductRun (initList steinerScaledProductMachine (encodeSteinerScaledProductRequest (factor,requests)))
      (haltList steinerScaledProductMachine (tallies (steinerScaledProduct (factor,requests))))
      (steinerScaledProductSteps (factor,requests))
    rw [scaledProduct_init,scaledProduct_halt]
    simpa only [paid,encodeSteinerScaledProductRequest,steinerScaledProduct,out] using all

theorem steinerScaledProductMachine_steps (request : SteinerScaledProductRequest) :
    (steinerScaledProductMachine_run request).steps = steinerScaledProductSteps request := rfl

/-- The exact run fits a cubic bound in the complete framed unary input. -/
theorem steinerScaledProductSteps_le (request : SteinerScaledProductRequest) :
    steinerScaledProductSteps request ≤ (encodeSteinerScaledProductRequest request).length^3+
      7*(encodeSteinerScaledProductRequest request).length^2+
      19*(encodeSteinerScaledProductRequest request).length+12 := by
  let f := request.1
  let v := steinerUnaryProductSum request.2
  let t := steinerUnaryProductSteps request.2
  let y := (encodeSteinerUnaryProductRequests request.2).length
  let x := (encodeSteinerScaledProductRequest request).length
  have xEq : x = f+(1+y) := by
    simp only [x,f,y,encodeSteinerScaledProductRequest,encodeSteinerUnaryProductCount,List.length_append,
      List.length_replicate,List.length_cons]
    omega
  have yFit : y ≤ x := by omega
  have factorFit : f ≤ x := by omega
  have powFit : y^2 ≤ x^2 := Nat.pow_le_pow_left yFit 2
  have tStart : t ≤ y^2+4*y+1 := steinerUnaryProductSteps_le request.2
  have tFit : t ≤ x^2+4*x+1 := by omega
  have vFit : 2*v ≤ t := steinerUnaryProductSum_twice_le_steps request.2
  have quant : 2*f*v ≤ x^3+4*x^2+x := calc
    _ = f*(2*v) := by ring
    _ ≤ x*(x^2+4*x+1) := Nat.mul_le_mul factorFit (vFit.trans tFit)
    _ = _ := by ring
  change t+2*f*v+6*f+3*v+9 ≤ x^3+7*x^2+19*x+12
  omega

/-- Polynomial certification for the scaled sum of products on unary input. -/
noncomputable def steinerScaledProductMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerScaledProductRequest encodeSteinerUnaryProductCount steinerScaledProduct where
  tm := steinerScaledProductMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X^3+Polynomial.C 7*Polynomial.X^2+Polynomial.C 19*Polynomial.X+Polynomial.C 12
  outputsFun request := by
    have run := steinerScaledProductMachine_run request
    change TM2OutputsInTime steinerScaledProductMachine ((encodeSteinerScaledProductRequest request).map id)
      (some ((encodeSteinerUnaryProductCount (steinerScaledProduct request)).map id)) _
    simpa only [List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_C] using
      (show TM2OutputsInTime steinerScaledProductMachine (encodeSteinerScaledProductRequest request)
        (some (encodeSteinerUnaryProductCount (steinerScaledProduct request))) _
        from ⟨run.toEvalsTo,run.steps_le_m.trans (steinerScaledProductSteps_le request)⟩)

section SeedBudget

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Present the three contributions to the fixed bit budget as operand
pairs, followed in the arithmetic by multiplication by the arc count. -/
def steinerSeedBudgetProductRequest {G : Arcs V} {height width : ℕ}
    (sizes : SteinerSeedDecoderSizes G height width) : SteinerScaledProductRequest :=
  (sizes.arcCount,[(sizes.earlyCount,width),(sizes.hubCount,2*sizes.vertexWidth),(sizes.arcCount,2*sizes.arcWidth)])

omit [LinearOrder V] in
theorem steinerSeedBudgetProductRequest_eq {G : Arcs V} {height width : ℕ}
    (sizes : SteinerSeedDecoderSizes G height width) :
    steinerScaledProduct (steinerSeedBudgetProductRequest sizes) = steinerBitBudgetFromDecoderSizes sizes := by
  simp [steinerScaledProduct,steinerSeedBudgetProductRequest,steinerUnaryProductSum,steinerBitBudgetFromDecoderSizes,
    Nat.add_assoc]

/-- Given the prepared decoder dimensions and correct forest width, the
actual machine returns the exact graph-dependent unary seed count. -/
def steinerScaledProductMachine_seedBudget {G : Arcs V} {height width : ℕ}
    (sizes : SteinerSeedDecoderSizes G height width) (width_eq : width = (forestScale G height).log2+1) :
    TM2OutputsInTime steinerScaledProductMachine (encodeSteinerScaledProductRequest (steinerSeedBudgetProductRequest sizes))
      (some (encodeSteinerUnaryProductCount (steinerBitBudget G height)))
      (steinerScaledProductSteps (steinerSeedBudgetProductRequest sizes)) := by
  rw [← steinerBitBudgetFromDecoderSizes_eq width_eq sizes,← steinerSeedBudgetProductRequest_eq sizes]
  exact steinerScaledProductMachine_run (steinerSeedBudgetProductRequest sizes)

end SeedBudget

end OnlineReachabilityPreservers
