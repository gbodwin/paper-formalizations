import OnlineReachabilityPreservers.SteinerScaledProductMachine
import OnlineReachabilityPreservers.SteinerSeedTapeMachine

/-! Compute the unary seed length from prepared dimensions before
sampling the supplied finite bit tape. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

/-- Left symbols carry arithmetic frames. Right symbols carry the bit
tape and the unary request markers for the sampler. -/
abbrev SteinerComputedSeedSymbol := Bool ⊕ Option Bool

private abbrev ComputedSeedCalcLabel := steinerScaledProductMachine.Λ
private abbrev ComputedSeedCalcRegister := steinerScaledProductMachine.σ
private abbrev ComputedSeedSamplerRegister := steinerSeedTapeMachine.σ
private instance : Fintype ComputedSeedCalcLabel := steinerScaledProductMachine.ΛFin

private inductive ComputedSeedLabel where
  | collect
  | restore
  | arithmetic (label : ComputedSeedCalcLabel)
  | transferCount
  | sample (label : Fin 4)
  deriving Fintype

private abbrev ComputedSeedRegister :=
  Option SteinerComputedSeedSymbol × ComputedSeedCalcRegister × ComputedSeedSamplerRegister
private abbrev ComputedSeedProgram :=
  StackMachineTag.Program (Fin 7) SteinerComputedSeedSymbol ComputedSeedLabel ComputedSeedRegister

private def computedSeedInitial : ComputedSeedRegister :=
  (none,steinerScaledProductMachine.initialState,steinerSeedTapeMachine.initialState)

private def computedSeedObserve (_ : ComputedSeedRegister) (seen : Option SteinerComputedSeedSymbol) :
    ComputedSeedRegister :=
  (seen,steinerScaledProductMachine.initialState,steinerSeedTapeMachine.initialState)

private def computedSeedReadCalc : SteinerComputedSeedSymbol → Option Bool
  | .inl bit => some bit
  | .inr _ => none

private def computedSeedCalcTag :
    StackMachineTag Bool SteinerComputedSeedSymbol ComputedSeedCalcLabel ComputedSeedLabel
      ComputedSeedCalcRegister ComputedSeedRegister where
  writeSymbol := Sum.inl
  readSymbol := computedSeedReadCalc
  writeRegister r := (none,r,steinerSeedTapeMachine.initialState)
  readRegister r := r.2.1
  writeLabel := .arithmetic
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def computedSeedSamplerTag :
    StackMachineTag (Option Bool) SteinerComputedSeedSymbol (Fin 4) ComputedSeedLabel
      ComputedSeedSamplerRegister ComputedSeedRegister where
  writeSymbol := Sum.inr
  readSymbol
    | .inl _ => none
    | .inr marker => some marker
  writeRegister r := (none,steinerScaledProductMachine.initialState,r)
  readRegister r := r.2.2
  writeLabel := .sample
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def computedSeedCalcSlots : Fin 6 ↪ Fin 7 :=
  ⟨Fin.castSucc,Fin.castSucc_injective _⟩

private def computedSeedSamplerSlots : Fin 3 ↪ Fin 7 where
  toFun := ![6,1,2]
  inj' := by
    intro i j same
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction

private def computedSeedCalcInner :
    ComputedSeedLabel →
      StackMachineTag.Program (Fin 6) SteinerComputedSeedSymbol ComputedSeedLabel ComputedSeedRegister
  | .arithmetic label =>
    computedSeedCalcTag.returningStatement .transferCount (steinerScaledProductMachine.m label)
  | _ => halt

private def computedSeedSamplerFramed (label : Fin 4) :
    StackMachineTag.Program (Fin 7) (Option Bool) (Fin 4) ComputedSeedSamplerRegister :=
  StackIndexEmbedding.statement computedSeedSamplerSlots (steinerSeedTapeMachine.m label)

private def computedSeedNext (label : ComputedSeedLabel) : ComputedSeedProgram :=
  load (fun _ => computedSeedInitial) (goto (fun _ => label))

private def computedSeedProgram : ComputedSeedLabel → ComputedSeedProgram
  | .collect =>
    peek 6 computedSeedObserve <|
      branch (fun r => (r.1.bind computedSeedReadCalc).isSome)
        (pop 6 (fun r _ => r) (push 5 (fun r => r.1.getD (Sum.inl false)) (computedSeedNext .collect)))
        (computedSeedNext .restore)
  | .restore =>
    pop 5 computedSeedObserve <|
      branch (fun r => r.1.isSome)
        (push 0 (fun r => r.1.getD (Sum.inl false)) (computedSeedNext .restore))
        (computedSeedNext (.arithmetic steinerScaledProductMachine.main))
  | .arithmetic label =>
    StackIndexEmbedding.statement computedSeedCalcSlots (computedSeedCalcInner (.arithmetic label))
  | .transferCount =>
    pop 4 computedSeedObserve <|
      branch (fun r => r.1.isSome)
        (push 6 (fun _ => Sum.inr none) (computedSeedNext .transferCount))
        (computedSeedNext (.sample steinerSeedTapeMachine.main))
  | .sample label => computedSeedSamplerTag.statement (computedSeedSamplerFramed label)

/-- Compute the seed length before running the verified sampler. The
bit tape stays on the seventh stack during the arithmetic. -/
abbrev steinerComputedSeedMachine : FinTM2 where
  K := Fin 7
  k₀ := 6
  k₁ := 6
  Γ _ := SteinerComputedSeedSymbol
  Λ := ComputedSeedLabel
  main := .collect
  σ := ComputedSeedRegister
  initialState := computedSeedInitial
  m := computedSeedProgram

private def computedSeedCfg (label : Option ComputedSeedLabel)
    (frame out buffer input : List SteinerComputedSeedSymbol) : steinerComputedSeedMachine.Cfg where
  l := label
  var := computedSeedInitial
  stk := ![frame,[],[],[],out,buffer,input]

private theorem computedSeed_update0 (a b c d word : List SteinerComputedSeedSymbol) :
    Function.update (![a,[],[],[],b,c,d] : Fin 7 → List SteinerComputedSeedSymbol) 0 word = ![word,[],[],[],b,c,d] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem computedSeed_update4 (a b c d word : List SteinerComputedSeedSymbol) :
    Function.update (![a,[],[],[],b,c,d] : Fin 7 → List SteinerComputedSeedSymbol) 4 word = ![a,[],[],[],word,c,d] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem computedSeed_update5 (a b c d word : List SteinerComputedSeedSymbol) :
    Function.update (![a,[],[],[],b,c,d] : Fin 7 → List SteinerComputedSeedSymbol) 5 word = ![a,[],[],[],b,word,d] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem computedSeed_update6 (a b c d word : List SteinerComputedSeedSymbol) :
    Function.update (![a,[],[],[],b,c,d] : Fin 7 → List SteinerComputedSeedSymbol) 6 word = ![a,[],[],[],b,c,word] := by
  funext i
  fin_cases i <;> simp [Function.update]

private def computedSeed_one {a b : steinerComputedSeedMachine.Cfg}
    (move : steinerComputedSeedMachine.step a = some b) :
    EvalsToInTime steinerComputedSeedMachine.step a (some b) 1 where
  steps := 1
  evals_in_steps := move
  steps_le_m := le_rfl

private theorem computedSeed_collectSymbol (bit : Bool) (buffer tail : List SteinerComputedSeedSymbol) :
    steinerComputedSeedMachine.step (computedSeedCfg (some .collect) [] [] buffer (Sum.inl bit::tail)) =
      some (computedSeedCfg (some .collect) [] [] (Sum.inl bit::buffer) tail) := by
  simp [FinTM2.step,steinerComputedSeedMachine,computedSeedCfg,Turing.TM2.step,Turing.TM2.stepAux,
    computedSeedProgram,computedSeedObserve,computedSeedNext,computedSeedReadCalc,computedSeed_update5,computedSeed_update6]
  rfl

private theorem computedSeed_collectDone (buffer : List SteinerComputedSeedSymbol) (seed : List (Option Bool)) :
    steinerComputedSeedMachine.step (computedSeedCfg (some .collect) [] [] buffer (seed.map Sum.inr)) =
      some (computedSeedCfg (some .restore) [] [] buffer (seed.map Sum.inr)) := by
  cases seed <;> simp [FinTM2.step,steinerComputedSeedMachine,computedSeedCfg,Turing.TM2.step,Turing.TM2.stepAux,
    computedSeedProgram,computedSeedObserve,computedSeedNext,computedSeedReadCalc] <;> rfl

private theorem computedSeed_restoreSymbol (symbol : SteinerComputedSeedSymbol)
    (buffer frame seed : List SteinerComputedSeedSymbol) :
    steinerComputedSeedMachine.step (computedSeedCfg (some .restore) frame [] (symbol::buffer) seed) =
      some (computedSeedCfg (some .restore) (symbol::frame) [] buffer seed) := by
  simp [FinTM2.step,steinerComputedSeedMachine,computedSeedCfg,Turing.TM2.step,Turing.TM2.stepAux,
    computedSeedProgram,computedSeedObserve,computedSeedNext,computedSeed_update0,computedSeed_update5]
  rfl

private theorem computedSeed_restoreDone (frame seed : List SteinerComputedSeedSymbol) :
    steinerComputedSeedMachine.step (computedSeedCfg (some .restore) frame [] [] seed) =
      some (computedSeedCfg (some (.arithmetic steinerScaledProductMachine.main)) frame [] [] seed) := by
  simp [FinTM2.step,steinerComputedSeedMachine,computedSeedCfg,Turing.TM2.step,Turing.TM2.stepAux,
    computedSeedProgram,computedSeedObserve,computedSeedNext,computedSeed_update5]
  rfl

private def computedSeed_collect (frame : List Bool) (buffer : List SteinerComputedSeedSymbol) (seed : List (Option Bool)) :
    EvalsToInTime steinerComputedSeedMachine.step
      (computedSeedCfg (some .collect) [] [] buffer (frame.map Sum.inl++seed.map Sum.inr))
      (some (computedSeedCfg (some .restore) [] [] ((frame.map Sum.inl).reverse++buffer) (seed.map Sum.inr)))
      (frame.length+1) := by
  induction frame generalizing buffer with
  | nil => exact computedSeed_one (computedSeed_collectDone buffer seed)
  | cons bit frame ih =>
    have first := computedSeed_one (computedSeed_collectSymbol bit buffer (frame.map Sum.inl++seed.map Sum.inr))
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (Sum.inl bit::buffer))
    simpa only [List.map_cons,List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,
      List.nil_append,List.length_cons] using all

private def computedSeed_restore (buffer frame seed : List SteinerComputedSeedSymbol) :
    EvalsToInTime steinerComputedSeedMachine.step
      (computedSeedCfg (some .restore) frame [] buffer seed)
      (some (computedSeedCfg (some (.arithmetic steinerScaledProductMachine.main)) (buffer.reverse++frame) [] [] seed))
      (buffer.length+1) := by
  induction buffer generalizing frame with
  | nil => exact computedSeed_one (computedSeed_restoreDone frame seed)
  | cons symbol buffer ih =>
    have first := computedSeed_one (computedSeed_restoreSymbol symbol buffer frame seed)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (symbol::frame))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons] using all

private theorem computedSeed_transferSymbol (symbol : SteinerComputedSeedSymbol)
    (remaining seed : List SteinerComputedSeedSymbol) :
    steinerComputedSeedMachine.step (computedSeedCfg (some .transferCount) [] (symbol::remaining) [] seed) =
      some (computedSeedCfg (some .transferCount) [] remaining [] (Sum.inr none::seed)) := by
  simp [FinTM2.step,steinerComputedSeedMachine,computedSeedCfg,Turing.TM2.step,Turing.TM2.stepAux,
    computedSeedProgram,computedSeedObserve,computedSeedNext,computedSeed_update4,computedSeed_update6]
  rfl

private theorem computedSeed_transferDone (seed : List SteinerComputedSeedSymbol) :
    steinerComputedSeedMachine.step (computedSeedCfg (some .transferCount) [] [] [] seed) =
      some (computedSeedCfg (some (.sample steinerSeedTapeMachine.main)) [] [] [] seed) := by
  simp [FinTM2.step,steinerComputedSeedMachine,computedSeedCfg,Turing.TM2.step,Turing.TM2.stepAux,
    computedSeedProgram,computedSeedObserve,computedSeedNext,computedSeed_update4]
  rfl

private def computedSeed_transfer (out : List SteinerComputedSeedSymbol) (seed : List (Option Bool)) :
    EvalsToInTime steinerComputedSeedMachine.step
      (computedSeedCfg (some .transferCount) [] out [] (seed.map Sum.inr))
      (some (computedSeedCfg (some (.sample steinerSeedTapeMachine.main)) [] [] []
        ((List.replicate out.length none++seed).map Sum.inr))) (out.length+1) := by
  induction out generalizing seed with
  | nil => exact computedSeed_one (computedSeed_transferDone (seed.map Sum.inr))
  | cons symbol out ih =>
    have first := computedSeed_one (computedSeed_transferSymbol symbol out (seed.map Sum.inr))
    have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (none::seed))
    have tally : List.replicate out.length none++none::seed = List.replicate (out.length+1) (none : Option Bool)++seed := by
      rw [List.replicate_succ',List.append_assoc,List.singleton_append]
    simpa only [tally,List.length_cons] using all

private def computedSeedPassive (seed : List (Option Bool)) (i : Fin 7) : List SteinerComputedSeedSymbol :=
  if i = 6 then seed.map Sum.inr else []

private theorem computedSeedCalcSlots_excludes_input (i : Fin 6) : computedSeedCalcSlots i ≠ 6 := by
  fin_cases i <;> decide

private noncomputable def computedSeedCalcTranslated (seed : List (Option Bool)) (c : steinerScaledProductMachine.Cfg) :
    steinerComputedSeedMachine.Cfg :=
  StackIndexEmbedding.configuration computedSeedCalcSlots (computedSeedPassive seed)
    (computedSeedCalcTag.returningConfiguration .transferCount c)

private theorem computedSeed_calcStep (seed : List (Option Bool)) {c after : steinerScaledProductMachine.Cfg}
    (move : steinerScaledProductMachine.step c = some after) :
    steinerComputedSeedMachine.step (computedSeedCalcTranslated seed c) = some (computedSeedCalcTranslated seed after) := by
  have tagged := computedSeedCalcTag.step_embedded_return .transferCount (base := steinerScaledProductMachine.m)
    (host := computedSeedCalcInner) (fun _ => rfl) move
  have framed := StackIndexEmbedding.step_on computedSeedCalcSlots (base := computedSeedCalcInner)
    (computedSeedPassive seed) (computedSeedCalcTag.returningConfiguration .transferCount c)
  rw [tagged] at framed
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact framed

private theorem computedSeed_calcTapes (seed : List (Option Bool)) (c : steinerScaledProductMachine.Cfg)
    (frame out : List Bool) (tapes : c.stk = ![frame,[],[],[],out,[]]) :
    (computedSeedCalcTranslated seed c).stk =
      ![frame.map Sum.inl,[],[],[],out.map Sum.inl,[],seed.map Sum.inr] := by
  have image (i : Fin 6) : (computedSeedCalcTranslated seed c).stk (computedSeedCalcSlots i) =
      ((![frame,[],[],[],out,[]] : Fin 6 → List Bool) i).map Sum.inl := by
    change StackIndexEmbedding.tapesAt computedSeedCalcSlots (fun i => (c.stk i).map Sum.inl) _
      (computedSeedCalcSlots i) = _
    rw [StackIndexEmbedding.tapesAt_image,tapes]
  funext i
  fin_cases i
  · exact image 0
  · exact image 1
  · exact image 2
  · exact image 3
  · exact image 4
  · exact image 5
  · change StackIndexEmbedding.tapesAt computedSeedCalcSlots _ (computedSeedPassive seed) 6 = _
    rw [StackIndexEmbedding.tapesAt_extra _ _ _ computedSeedCalcSlots_excludes_input,computedSeedPassive,ite_eq_left rfl]
    rfl

private theorem computedSeed_calcInit (frame : List Bool) (seed : List (Option Bool)) :
    computedSeedCalcTranslated seed (initList steinerScaledProductMachine frame) =
      computedSeedCfg (some (.arithmetic steinerScaledProductMachine.main)) (frame.map Sum.inl) [] [] (seed.map Sum.inr) := by
  apply congrArg (fun stk : Fin 7 → List SteinerComputedSeedSymbol =>
    (⟨some (.arithmetic steinerScaledProductMachine.main),computedSeedInitial,stk⟩ : steinerComputedSeedMachine.Cfg))
  exact computedSeed_calcTapes seed (initList steinerScaledProductMachine frame) frame [] (by
    funext i
    fin_cases i <;> rfl)

private theorem computedSeed_calcReturn (out : List Bool) (seed : List (Option Bool)) :
    computedSeedCalcTranslated seed (haltList steinerScaledProductMachine out) =
      computedSeedCfg (some .transferCount) [] (out.map Sum.inl) [] (seed.map Sum.inr) := by
  apply congrArg (fun stk : Fin 7 → List SteinerComputedSeedSymbol =>
    (⟨some .transferCount,computedSeedInitial,stk⟩ : steinerComputedSeedMachine.Cfg))
  exact computedSeed_calcTapes seed (haltList steinerScaledProductMachine out) [] out (by
    funext i
    fin_cases i <;> rfl)

private def computedSeed_arithmetic (request : SteinerScaledProductRequest) (seed : List (Option Bool)) :
    EvalsToInTime steinerComputedSeedMachine.step
      (computedSeedCfg (some (.arithmetic steinerScaledProductMachine.main))
        ((encodeSteinerScaledProductRequest request).map Sum.inl) [] [] (seed.map Sum.inr))
      (some (computedSeedCfg (some .transferCount) []
        ((encodeSteinerUnaryProductCount (steinerScaledProduct request)).map Sum.inl) [] (seed.map Sum.inr)))
      (steinerScaledProductSteps request) := by
  let run := steinerScaledProductMachine_run request
  refine ⟨⟨run.steps,?_⟩,run.steps_le_m⟩
  have evaluated := iterate_map_some (computedSeedCalcTranslated seed) (fun move => computedSeed_calcStep seed move)
    run.steps run.evals_in_steps
  change (flip bind steinerComputedSeedMachine.step)^[run.steps]
      (some (computedSeedCalcTranslated seed (initList steinerScaledProductMachine (encodeSteinerScaledProductRequest request)))) =
    some (computedSeedCalcTranslated seed
      (haltList steinerScaledProductMachine (encodeSteinerUnaryProductCount (steinerScaledProduct request)))) at evaluated
  rw [computedSeed_calcInit,computedSeed_calcReturn] at evaluated
  exact evaluated

private noncomputable def computedSeedSamplerTranslated (c : steinerSeedTapeMachine.Cfg) : steinerComputedSeedMachine.Cfg :=
  computedSeedSamplerTag.configuration (StackIndexEmbedding.configuration computedSeedSamplerSlots (fun _ => []) c)

private theorem computedSeed_sampleTapes (c : steinerSeedTapeMachine.Cfg) (word : List (Option Bool))
    (tapes : c.stk = ![word,[],[]]) :
    (computedSeedSamplerTranslated c).stk = ![[],[],[],[],[],[],word.map Sum.inr] := by
  have image (i : Fin 3) : (computedSeedSamplerTranslated c).stk (computedSeedSamplerSlots i) =
      ((![word,[],[]] : Fin 3 → List (Option Bool)) i).map Sum.inr := by
    change (StackIndexEmbedding.tapesAt computedSeedSamplerSlots c.stk (fun _ => []) (computedSeedSamplerSlots i)).map Sum.inr = _
    rw [StackIndexEmbedding.tapesAt_image,tapes]
  have extra (i : Fin 7) (outside : ∀ j, computedSeedSamplerSlots j ≠ i) :
      (computedSeedSamplerTranslated c).stk i = [] := by
    change (StackIndexEmbedding.tapesAt computedSeedSamplerSlots _ (fun _ => []) i).map Sum.inr = []
    rw [StackIndexEmbedding.tapesAt_extra _ _ _ outside]
    rfl
  funext i
  fin_cases i
  · exact extra 0 (by intro j; fin_cases j <;> decide)
  · exact image 1
  · exact image 2
  · exact extra 3 (by intro j; fin_cases j <;> decide)
  · exact extra 4 (by intro j; fin_cases j <;> decide)
  · exact extra 5 (by intro j; fin_cases j <;> decide)
  · exact image 0

private theorem computedSeed_sampleInit (seed : List (Option Bool)) :
    computedSeedSamplerTranslated (initList steinerSeedTapeMachine seed) =
      computedSeedCfg (some (.sample steinerSeedTapeMachine.main)) [] [] [] (seed.map Sum.inr) := by
  apply congrArg (fun stk : Fin 7 → List SteinerComputedSeedSymbol =>
    (⟨some (.sample steinerSeedTapeMachine.main),computedSeedInitial,stk⟩ : steinerComputedSeedMachine.Cfg))
  apply computedSeed_sampleTapes
  funext i
  fin_cases i <;> rfl

private theorem computedSeed_sampleHalt (seed : List (Option Bool)) :
    computedSeedSamplerTranslated (haltList steinerSeedTapeMachine seed) =
      haltList steinerComputedSeedMachine (seed.map Sum.inr) := by
  apply congrArg (fun stk : Fin 7 → List SteinerComputedSeedSymbol =>
    (⟨none,computedSeedInitial,stk⟩ : steinerComputedSeedMachine.Cfg))
  have source : (haltList steinerSeedTapeMachine seed).stk = ![seed,[],[]] := by
    funext i
    fin_cases i <;> rfl
  have target : (haltList steinerComputedSeedMachine (seed.map Sum.inr)).stk = ![[],[],[],[],[],[],seed.map Sum.inr] := by
    funext i
    fin_cases i <;> rfl
  exact (computedSeed_sampleTapes _ _ source).trans target.symm

private def computedSeed_sample (seed out : List (Option Bool)) {bound : ℕ}
    (run : TM2OutputsInTime steinerSeedTapeMachine seed (some out) bound) :
    EvalsToInTime steinerComputedSeedMachine.step
      (computedSeedCfg (some (.sample steinerSeedTapeMachine.main)) [] [] [] (seed.map Sum.inr))
      (some (haltList steinerComputedSeedMachine (out.map Sum.inr))) bound := by
  refine ⟨⟨run.steps,?_⟩,run.steps_le_m⟩
  let framed := StackIndexEmbedding.evaluation computedSeedSamplerSlots (base := steinerSeedTapeMachine.m) (fun _ => []) run
  let tagged := computedSeedSamplerTag.evaluation (base := computedSeedSamplerFramed) (host := computedSeedProgram) (fun _ => rfl) framed
  have evaluated : (flip bind steinerComputedSeedMachine.step)^[run.steps]
      (some (computedSeedSamplerTranslated (initList steinerSeedTapeMachine seed))) =
    some (computedSeedSamplerTranslated (haltList steinerSeedTapeMachine out)) := tagged.evals_in_steps
  rw [computedSeed_sampleInit,computedSeed_sampleHalt] at evaluated
  exact evaluated

private theorem computedSeed_init (input : List SteinerComputedSeedSymbol) :
    initList steinerComputedSeedMachine input = computedSeedCfg (some .collect) [] [] [] input := by
  apply congrArg (fun stk : Fin 7 → List SteinerComputedSeedSymbol =>
    (⟨some .collect,computedSeedInitial,stk⟩ : steinerComputedSeedMachine.Cfg))
  funext i
  fin_cases i <;> rfl

abbrev SteinerComputedSeedRequest := SteinerScaledProductRequest × List Bool

/-- The encoded dimensions precede the finite bit tape. The count
markers are built by the machine. -/
def encodeSteinerComputedSeed (request : SteinerComputedSeedRequest) : List SteinerComputedSeedSymbol :=
  (encodeSteinerScaledProductRequest request.1).map Sum.inl ++ (request.2.map some).map Sum.inr

def steinerComputedSeedAnswer (request : SteinerComputedSeedRequest) : List SteinerComputedSeedSymbol :=
  (splitSteinerSeedTapeOrReject (steinerScaledProduct request.1,request.2)).map Sum.inr

private def computedSeed_execute (request : SteinerScaledProductRequest) (tape : List Bool) (out : List (Option Bool))
    {bound : ℕ}
    (sampler : TM2OutputsInTime steinerSeedTapeMachine
      (encodeSteinerSeedTapeRequest (steinerScaledProduct request,tape)) (some out) bound) :
    TM2OutputsInTime steinerComputedSeedMachine (encodeSteinerComputedSeed (request,tape))
      (some (out.map Sum.inr))
      (2*(encodeSteinerScaledProductRequest request).length+steinerScaledProductSteps request+
        steinerScaledProduct request+bound+3) := by
  let frame := encodeSteinerScaledProductRequest request
  let seed := tape.map some
  let count := steinerScaledProduct request
  let tallies : List SteinerComputedSeedSymbol := (encodeSteinerUnaryProductCount count).map Sum.inl
  have collected := computedSeed_collect frame [] seed
  rw [List.append_nil] at collected
  have restored := computedSeed_restore (frame.map Sum.inl).reverse [] (seed.map Sum.inr)
  rw [List.reverse_reverse,List.append_nil,List.length_reverse,List.length_map] at restored
  have prepared := EvalsToInTime.trans _ _ _ _ _ _ collected restored
  have arithmetic := EvalsToInTime.trans _ _ _ _ _ _ prepared (computedSeed_arithmetic request seed)
  have transferred := computedSeed_transfer tallies seed
  have countLength : tallies.length = count := by simp [tallies,encodeSteinerUnaryProductCount]
  rw [countLength] at transferred
  have ready := EvalsToInTime.trans _ _ _ _ _ _ arithmetic transferred
  have all := EvalsToInTime.trans _ _ _ _ _ _ ready
    (computedSeed_sample (encodeSteinerSeedTapeRequest (count,tape)) out sampler)
  change EvalsToInTime steinerComputedSeedMachine.step _ (some (haltList steinerComputedSeedMachine _)) _
  rw [computedSeed_init]
  exact ⟨all.toEvalsTo,by have spent := all.steps_le_m; dsimp only [frame,count] at spent; omega⟩

/-- Compute the count, place its unary markers before the tape, and
sample exactly the specified finite prefix or report exhaustion. -/
def steinerComputedSeedMachine_run (request : SteinerComputedSeedRequest) :
    TM2OutputsInTime steinerComputedSeedMachine (encodeSteinerComputedSeed request)
      (some (steinerComputedSeedAnswer request))
      (2*(encodeSteinerScaledProductRequest request.1).length+steinerScaledProductSteps request.1+
        4*steinerScaledProduct request.1+6) := by
  let pair := (steinerScaledProduct request.1,request.2)
  have run := computedSeed_execute request.1 request.2 _ (steinerSeedTapeMachine_runOrReject pair)
  exact ⟨run.toEvalsTo,by have spent := run.steps_le_m; dsimp only [pair] at spent; omega⟩

/-- The output is empty exactly when the computed count exceeds the
number of supplied bits. -/
theorem steinerComputedSeedAnswer_eq_nil_iff (request : SteinerComputedSeedRequest) :
    steinerComputedSeedAnswer request = [] ↔ request.2.length < steinerScaledProduct request.1 := by
  simp [steinerComputedSeedAnswer,splitSteinerSeedTapeOrReject_eq_nil_iff]

/-- The composed transition bound is cubic in the actual framed unary
dimensions and finite bit tape. -/
noncomputable def steinerComputedSeedMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerComputedSeed id steinerComputedSeedAnswer where
  tm := steinerComputedSeedMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 3*Polynomial.X^3+Polynomial.C 21*Polynomial.X^2+Polynomial.C 59*Polynomial.X+Polynomial.C 42
  outputsFun request := by
    let y := (encodeSteinerScaledProductRequest request.1).length
    let x := (encodeSteinerComputedSeed request).length
    have input : x = y+request.2.length := by
      simp only [x,y,encodeSteinerComputedSeed,List.length_append,List.length_map]
    have size : y ≤ x := by omega
    have square := Nat.pow_le_pow_left size 2
    have cube := Nat.pow_le_pow_left size 3
    have work : steinerScaledProductSteps request.1 ≤ y^3+7*y^2+19*y+12 :=
      steinerScaledProductSteps_le request.1
    have units : 2*steinerScaledProduct request.1 ≤ steinerScaledProductSteps request.1 := by
      let f := request.1.1
      let s := steinerUnaryProductSum request.1.2
      change 2*(s*f) ≤ steinerUnaryProductSteps request.1.2+2*f*s+6*f+3*s+9
      rw [show 2*(s*f) = 2*f*s by ring]
      omega
    have fits : 2*y+steinerScaledProductSteps request.1+4*steinerScaledProduct request.1+6 ≤
        3*x^3+21*x^2+59*x+42 := by omega
    have run := steinerComputedSeedMachine_run request
    change TM2OutputsInTime steinerComputedSeedMachine ((encodeSteinerComputedSeed request).map id)
      (some ((steinerComputedSeedAnswer request).map id)) _
    simpa only [List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_C,x] using
      (show TM2OutputsInTime steinerComputedSeedMachine (encodeSteinerComputedSeed request)
        (some (steinerComputedSeedAnswer request)) _ from
        ⟨run.toEvalsTo,run.steps_le_m.trans fits⟩)

/-- With prepared dimensions and the certified forest width, the
machine computes the exact graph bit budget and implements the
finite sampler on every supplied tape. -/
def steinerComputedSeedMachine_finiteSampler {V : Type*} [LinearOrder V] [Fintype V] {G : Arcs V}
    {height width : ℕ} (sizes : SteinerSeedDecoderSizes G height width)
    (width_eq : width = (forestScale G height).log2+1) (tape : List Bool) :
    let request := steinerSeedBudgetProductRequest sizes
    let count : {b : ℕ // b = steinerBitBudget G height} := ⟨_,rfl⟩
    TM2OutputsInTime steinerComputedSeedMachine (encodeSteinerComputedSeed (request,tape))
      (some (((((readSteinerSeedWithWork count steinerBitTapeSource).run tape).map encodeSavedSteinerSeed).getD []).map Sum.inr))
      (2*(encodeSteinerScaledProductRequest request).length+steinerScaledProductSteps request+4*steinerBitBudget G height+6) := by
  let request := steinerSeedBudgetProductRequest sizes
  let count : {b : ℕ // b = steinerBitBudget G height} := ⟨_,rfl⟩
  let out := (((readSteinerSeedWithWork count steinerBitTapeSource).run tape).map encodeSavedSteinerSeed).getD []
  have countEq : steinerScaledProduct request = steinerBitBudget G height :=
    (steinerSeedBudgetProductRequest_eq sizes).trans (steinerBitBudgetFromDecoderSizes_eq width_eq sizes)
  have sampler : TM2OutputsInTime steinerSeedTapeMachine (encodeSteinerSeedTapeRequest (steinerScaledProduct request,tape))
      (some out) (3*steinerBitBudget G height+3) := by
    rw [countEq]
    exact steinerSeedTapeMachine_refinesFiniteSampler count tape
  have run := computedSeed_execute request tape out sampler
  refine ⟨run.toEvalsTo,run.steps_le_m.trans ?_⟩
  change _ ≤ 2*(encodeSteinerScaledProductRequest request).length+steinerScaledProductSteps request+
    4*steinerBitBudget G height+6
  rw [countEq]
  omega

end OnlineReachabilityPreservers
