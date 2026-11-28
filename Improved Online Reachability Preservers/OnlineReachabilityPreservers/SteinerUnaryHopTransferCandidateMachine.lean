import OnlineReachabilityPreservers.SteinerDistanceHopTransferRows
import OnlineReachabilityPreservers.SteinerUnaryRoundTotalMachine

/-! Compute one unary distance candidate from a capped transfer code. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev CandidateSymbol := SteinerUnaryCappedRowsSymbol

private inductive CandidateCode where
  | zero | one | missing
  deriving DecidableEq

private instance : Fintype CandidateCode where
  elems := {.zero,.one,.missing}
  complete code := by cases code <;> decide

private def CandidateCode.next : CandidateCode → CandidateCode
  | .zero => .one
  | _ => .missing

private def classifyCandidateCode : ℕ → CandidateCode
  | 0 => .zero
  | 1 => .one
  | _+2 => .missing

private theorem classifyCandidateCode_succ (code : ℕ) :
    classifyCandidateCode (code+1) = (classifyCandidateCode code).next := by
  rcases code with _ | _ | code <;> rfl

private inductive CandidateLabel where
  | cap | code (seen : CandidateCode) | prior (keep : Bool) | finish (emitCap : Bool)
  deriving Fintype

private abbrev CandidateRegister := Option CandidateSymbol
private abbrev CandidateProgram := StackMachineTag.Program (Fin 3) CandidateSymbol CandidateLabel CandidateRegister

private def candidateTally : CandidateSymbol := Sum.inr (some true)
private def candidateField : CandidateSymbol := Sum.inr none
private abbrev candidateTallies := encodeSteinerUnaryRoundTotal

private def candidateIsTally : CandidateRegister → Bool
  | some (.inr (some true)) => true
  | _ => false

private def candidatePop (slot : Fin 3) (next : CandidateProgram) : CandidateProgram :=
  pop slot (fun _ seen => seen) next

private def candidatePush (slot : Fin 3) (next : CandidateProgram) : CandidateProgram :=
  push slot (fun _ => candidateTally) next

private def candidateGoto (label : CandidateLabel) : CandidateProgram :=
  load (fun _ => none) (goto fun _ => label)

private def candidateContinueCode : CandidateCode → CandidateProgram
  | .zero => candidateGoto (.prior true)
  | .one => candidatePush 2 (candidateGoto (.prior true))
  | .missing => candidateGoto (.prior false)

private def candidatePriorCode : Bool → CandidateProgram
  | true => candidatePush 2 (candidateGoto (.prior true))
  | false => candidateGoto (.prior false)

private def candidateFinishCode : Bool → CandidateProgram
  | true => candidatePush 2 (candidateGoto (.finish true))
  | false => candidateGoto (.finish false)

private def candidateProgram : CandidateLabel → CandidateProgram
  | .cap => candidatePop 0 <| branch candidateIsTally
      (candidatePush 1 (candidateGoto .cap)) (candidateGoto (.code .zero))
  | .code seen => candidatePop 0 <| branch candidateIsTally
      (candidateGoto (.code seen.next)) (candidateContinueCode seen)
  | .prior keep => candidatePop 0 <| branch candidateIsTally
      (candidatePriorCode keep) (candidateGoto (.finish (!keep)))
  | .finish emitCap => candidatePop 1 <| branch Option.isSome
      (candidateFinishCode emitCap) (load (fun _ => none) halt)

/-- Code zero keeps the prior, code one adds a tally, and every
larger code emits the cap. -/
abbrev steinerUnaryHopTransferCandidateMachine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ _ := CandidateSymbol
  Λ := CandidateLabel
  main := .cap
  σ := CandidateRegister
  initialState := none
  m := candidateProgram

private def candidateTapes (word : List CandidateSymbol) (cap out : ℕ) : Fin 3 → List CandidateSymbol :=
  ![word,candidateTallies cap,candidateTallies out]

private def candidateCfg (label : Option CandidateLabel) (word : List CandidateSymbol) (cap out : ℕ) :
    steinerUnaryHopTransferCandidateMachine.Cfg := ⟨label,none,candidateTapes word cap out⟩

private theorem candidate_update0 (word next : List CandidateSymbol) (cap out : ℕ) :
    Function.update (candidateTapes word cap out) 0 next = candidateTapes next cap out := by
  funext i
  fin_cases i <;> simp [candidateTapes,Function.update]

private theorem candidate_update1 (word : List CandidateSymbol) (cap out value : ℕ) :
    Function.update (candidateTapes word cap out) 1 (candidateTallies value) = candidateTapes word value out := by
  funext i
  fin_cases i <;> simp [candidateTapes,Function.update]

private theorem candidate_update2 (word : List CandidateSymbol) (cap out value : ℕ) :
    Function.update (candidateTapes word cap out) 2 (candidateTallies value) = candidateTapes word cap value := by
  funext i
  fin_cases i <;> simp [candidateTapes,Function.update]

private abbrev CandidateRun (a b : steinerUnaryHopTransferCandidateMachine.Cfg) (time : ℕ) :=
  EvalsToInTime steinerUnaryHopTransferCandidateMachine.step a (some b) time

private def candidateOne {a b : steinerUnaryHopTransferCandidateMachine.Cfg}
    (step : steinerUnaryHopTransferCandidateMachine.step a = some b) : CandidateRun a b 1 := ⟨⟨1,step⟩,le_rfl⟩

private def candidateThen {a b c : steinerUnaryHopTransferCandidateMachine.Cfg} {x y : ℕ}
    (first : CandidateRun a b x) (second : CandidateRun b c y) : CandidateRun a c (x+y) := by
  simpa only [Nat.add_comm] using EvalsToInTime.trans _ _ _ _ _ _ first second

private def candidateRelax {a b : steinerUnaryHopTransferCandidateMachine.Cfg} {x y : ℕ}
    (run : CandidateRun a b x) (le : x ≤ y) : CandidateRun a b y := ⟨run.toEvalsTo,run.steps_le_m.trans le⟩

private theorem candidateTallies_succ (n : ℕ) : candidateTallies (n+1) = candidateTally::candidateTallies n := rfl

private theorem candidateCap_push (word : List CandidateSymbol) (stored : ℕ) :
    steinerUnaryHopTransferCandidateMachine.step (candidateCfg (some .cap) (candidateTally::word) stored 0) =
      some (candidateCfg (some .cap) word (stored+1) 0) := by
  simp only [FinTM2.step,steinerUnaryHopTransferCandidateMachine,candidateCfg,Turing.TM2.step,Turing.TM2.stepAux,
    candidateProgram,candidatePop,candidatePush,candidateGoto,candidate_update0]
  change some (⟨some .cap,none,Function.update (candidateTapes word stored 0) 1 (candidateTallies (stored+1))⟩ :
    steinerUnaryHopTransferCandidateMachine.Cfg) = _
  rw [candidate_update1]
  rfl

private theorem candidateCap_end (word : List CandidateSymbol) (stored : ℕ) :
    steinerUnaryHopTransferCandidateMachine.step (candidateCfg (some .cap) (candidateField::word) stored 0) =
      some (candidateCfg (some (.code .zero)) word stored 0) := by
  simp only [FinTM2.step,steinerUnaryHopTransferCandidateMachine,candidateCfg,Turing.TM2.step,Turing.TM2.stepAux,
    candidateProgram,candidatePop,candidatePush,candidateGoto,candidate_update0]
  rfl

private def candidateCap (cap : ℕ) (word : List CandidateSymbol) (stored : ℕ) :
    CandidateRun (candidateCfg (some .cap) (candidateTallies cap++candidateField::word) stored 0)
      (candidateCfg (some (.code .zero)) word (stored+cap) 0) (cap+1) := by
  induction cap generalizing stored with
  | zero => exact candidateOne (candidateCap_end word stored)
  | succ cap ih =>
    have run := candidateThen (candidateOne (candidateCap_push _ stored)) (ih (stored+1))
    simpa only [candidateTallies_succ,List.cons_append,Nat.add_right_comm,Nat.add_assoc,Nat.add_left_comm] using run

private theorem candidateCode_read (word : List CandidateSymbol) (stored : ℕ) (seen : CandidateCode) :
    steinerUnaryHopTransferCandidateMachine.step (candidateCfg (some (.code seen)) (candidateTally::word) stored 0) =
      some (candidateCfg (some (.code seen.next)) word stored 0) := by
  simp only [FinTM2.step,steinerUnaryHopTransferCandidateMachine,candidateCfg,Turing.TM2.step,Turing.TM2.stepAux,
    candidateProgram,candidatePop,candidateGoto,candidate_update0]
  rfl

private def candidateCodeRead (code : ℕ) (word : List CandidateSymbol) (stored base : ℕ) :
    CandidateRun (candidateCfg (some (.code (classifyCandidateCode base))) (candidateTallies code++word) stored 0)
      (candidateCfg (some (.code (classifyCandidateCode (base+code)))) word stored 0) code := by
  induction code generalizing base with
  | zero => exact ⟨⟨0,rfl⟩,le_rfl⟩
  | succ code ih =>
    have first := candidateOne (candidateCode_read (candidateTallies code++word) stored (classifyCandidateCode base))
    rw [← classifyCandidateCode_succ] at first
    have run := candidateThen first (ih (base+1))
    simpa [candidateTallies_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using run

private def candidateKeep : CandidateCode → Bool
  | .missing => false
  | _ => true

private def candidateExtra : CandidateCode → ℕ
  | .one => 1
  | _ => 0

private theorem candidateCode_end (word : List CandidateSymbol) (stored : ℕ) (code : CandidateCode) :
    steinerUnaryHopTransferCandidateMachine.step (candidateCfg (some (.code code)) (candidateField::word) stored 0) =
      some (candidateCfg (some (.prior (candidateKeep code))) word stored (candidateExtra code)) := by
  cases code <;> simp only [FinTM2.step,steinerUnaryHopTransferCandidateMachine,candidateCfg,Turing.TM2.step,Turing.TM2.stepAux,
    candidateProgram,candidatePop,candidateContinueCode,candidatePush,candidateGoto,candidateKeep,candidateExtra,
    candidate_update0]
  · rfl
  · change some (⟨some (.prior true),none,Function.update (candidateTapes word stored 0) 2 (candidateTallies 1)⟩ :
      steinerUnaryHopTransferCandidateMachine.Cfg) = _
    rw [candidate_update2]
    rfl
  · rfl

private theorem candidatePrior_push (keep : Bool) (word : List CandidateSymbol) (stored out : ℕ) :
    steinerUnaryHopTransferCandidateMachine.step (candidateCfg (some (.prior keep)) (candidateTally::word) stored out) =
      some (candidateCfg (some (.prior keep)) word stored (out+(if keep then 1 else 0))) := by
  cases keep <;> simp only [FinTM2.step,steinerUnaryHopTransferCandidateMachine,candidateCfg,Turing.TM2.step,Turing.TM2.stepAux,
    candidateProgram,candidatePop,candidatePriorCode,candidatePush,candidateGoto,candidate_update0]
  · rfl
  · change some (⟨some (.prior true),none,Function.update (candidateTapes word stored out) 2 (candidateTallies (out+1))⟩ :
      steinerUnaryHopTransferCandidateMachine.Cfg) = _
    rw [candidate_update2]
    rfl

private theorem candidatePrior_end (keep : Bool) (stored out : ℕ) :
    steinerUnaryHopTransferCandidateMachine.step (candidateCfg (some (.prior keep)) [candidateField] stored out) =
      some (candidateCfg (some (.finish (!keep))) [] stored out) := by
  simp only [FinTM2.step,steinerUnaryHopTransferCandidateMachine,candidateCfg,Turing.TM2.step,Turing.TM2.stepAux,
    candidateProgram,candidatePop,candidateGoto,candidate_update0]
  rfl

private def candidatePrior (keep : Bool) (prior stored out : ℕ) :
    CandidateRun (candidateCfg (some (.prior keep)) (candidateTallies prior++[candidateField]) stored out)
      (candidateCfg (some (.finish (!keep))) [] stored (out+(if keep then prior else 0))) (prior+1) := by
  induction prior generalizing out with
  | zero =>
    cases keep <;> exact candidateOne (candidatePrior_end _ _ _)
  | succ prior ih =>
    have run := candidateThen (candidateOne (candidatePrior_push keep _ stored out))
      (ih (out+(if keep then 1 else 0)))
    cases keep <;> simpa [candidateTallies_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using run

private theorem candidateFinish_push (emitCap : Bool) (stored out : ℕ) :
    steinerUnaryHopTransferCandidateMachine.step (candidateCfg (some (.finish emitCap)) [] (stored+1) out) =
      some (candidateCfg (some (.finish emitCap)) [] stored (out+(if emitCap then 1 else 0))) := by
  cases emitCap <;> simp only [FinTM2.step,steinerUnaryHopTransferCandidateMachine,candidateCfg,Turing.TM2.step,Turing.TM2.stepAux,
    candidateProgram,candidatePop,candidateFinishCode,candidatePush,candidateGoto]
  · change some (⟨some (.finish false),none,Function.update _ 1 (candidateTallies stored)⟩ :
      steinerUnaryHopTransferCandidateMachine.Cfg) = _
    rw [candidate_update1]
    rfl
  · change some (⟨some (.finish true),none,Function.update (Function.update _ 1 (candidateTallies stored)) 2
      (candidateTallies (out+1))⟩ : steinerUnaryHopTransferCandidateMachine.Cfg) = _
    rw [candidate_update1,candidate_update2]
    rfl

private theorem candidateFinish_end (emitCap : Bool) (out : ℕ) :
    steinerUnaryHopTransferCandidateMachine.step (candidateCfg (some (.finish emitCap)) [] 0 out) =
      some (candidateCfg none [] 0 out) := by
  simp only [FinTM2.step,steinerUnaryHopTransferCandidateMachine,candidateCfg,Turing.TM2.step,Turing.TM2.stepAux,
    candidateProgram,candidatePop]
  change some (⟨none,none,Function.update _ 1 (candidateTallies 0)⟩ : steinerUnaryHopTransferCandidateMachine.Cfg) = _
  rw [candidate_update1]
  rfl

private def candidateFinish (emitCap : Bool) (stored out : ℕ) :
    CandidateRun (candidateCfg (some (.finish emitCap)) [] stored out)
      (candidateCfg none [] 0 (out+(if emitCap then stored else 0))) (stored+1) := by
  induction stored generalizing out with
  | zero => cases emitCap <;> exact candidateOne (candidateFinish_end _ _)
  | succ stored ih =>
    have run := candidateThen (candidateOne (candidateFinish_push emitCap stored out))
      (ih (out+(if emitCap then 1 else 0)))
    cases emitCap <;> simpa [candidateTallies_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using run

private theorem candidateClass_eq (cap code prior : ℕ) :
    let seen := classifyCandidateCode code
    candidateExtra seen+(if candidateKeep seen then prior else 0)+(if !candidateKeep seen then cap else 0) =
      if code ≤ 1 then prior+code else cap := by
  rcases code with _ | _ | code <;>
    simp [classifyCandidateCode,candidateExtra,candidateKeep,Nat.add_comm]

/-- Supply the cap, transfer code, and previous value as unary fields. -/
def encodeSteinerUnaryHopTransferCandidate (request : ℕ × ℕ × ℕ) : List SteinerUnaryCappedRowsSymbol :=
  encodeSteinerUnaryRoundPriorVector [request.1,request.2.1,request.2.2]

/-- Three field delimiters follow the three unary operands. -/
theorem encodeSteinerUnaryHopTransferCandidate_length (cap code prior : ℕ) :
    (encodeSteinerUnaryHopTransferCandidate (cap,code,prior)).length = cap+code+prior+3 := by
  rw [encodeSteinerUnaryHopTransferCandidate,encodeSteinerUnaryRoundPriorVector_length]
  simp only [List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega

private theorem candidate_Init (word : List CandidateSymbol) :
    initList steinerUnaryHopTransferCandidateMachine word = candidateCfg (some .cap) word 0 0 := by
  apply congrArg (fun tapes : Fin 3 → List CandidateSymbol =>
    (⟨some .cap,none,tapes⟩ : steinerUnaryHopTransferCandidateMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem candidate_Halt (out : ℕ) :
    haltList steinerUnaryHopTransferCandidateMachine (encodeSteinerUnaryRoundTotal out) = candidateCfg none [] 0 out := by
  apply congrArg (fun tapes : Fin 3 → List CandidateSymbol =>
    (⟨none,none,tapes⟩ : steinerUnaryHopTransferCandidateMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- Native evaluation of the supplied three unary fields, in linear
transition time. -/
def steinerUnaryHopTransferCandidateMachine_run (cap code prior : ℕ) :
    let input := encodeSteinerUnaryHopTransferCandidate (cap,code,prior)
    TM2OutputsInTime steinerUnaryHopTransferCandidateMachine input
      (some (encodeSteinerUnaryRoundTotal (if code ≤ 1 then prior+code else cap))) (2*input.length) := by
  let suffix := candidateTallies prior++[candidateField]
  let payload := candidateTallies code++candidateField::suffix
  let seen := classifyCandidateCode code
  have field := candidateCap cap payload 0
  simp only [Nat.zero_add] at field
  have read := candidateCodeRead code (candidateField::suffix) cap 0
  simp only [Nat.zero_add] at read
  have endCode := candidateOne (candidateCode_end suffix cap seen)
  have takeValue := candidatePrior (candidateKeep seen) prior cap (candidateExtra seen)
  have finish := candidateFinish (!candidateKeep seen) cap (candidateExtra seen+(if candidateKeep seen then prior else 0))
  rw [candidateClass_eq cap code prior] at finish
  have run := candidateThen (candidateThen (candidateThen (candidateThen field read) endCode) takeValue) finish
  have layout : encodeSteinerUnaryHopTransferCandidate (cap,code,prior) =
      candidateTallies cap++candidateField::payload := by
    simp only [encodeSteinerUnaryHopTransferCandidate,encodeSteinerUnaryRoundPriorVector,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.append_assoc,List.singleton_append,payload,suffix,candidateField,encodeSteinerUnaryRoundTotal]
    rfl
  dsimp only
  change CandidateRun (initList steinerUnaryHopTransferCandidateMachine _) (haltList steinerUnaryHopTransferCandidateMachine _) _
  rw [candidate_Init,candidate_Halt,encodeSteinerUnaryHopTransferCandidate_length,layout]
  refine candidateRelax run ?_
  omega

/-- The actual transition bound grows linearly with the unary input. -/
noncomputable def steinerUnaryHopTransferCandidateMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryHopTransferCandidate encodeSteinerUnaryRoundTotal
      (fun r => if r.2.1 ≤ 1 then r.2.2+r.2.1 else r.1) where
  tm := steinerUnaryHopTransferCandidateMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2*Polynomial.X
  outputsFun request := by
    rcases request with ⟨cap,code,prior⟩
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_C_mul,Polynomial.eval_X] using
      steinerUnaryHopTransferCandidateMachine_run cap code prior

/-- Evaluate the exact transfer candidate for one supplied source and
successor in the previous distance column. -/
def steinerUnaryHopTransferCandidateMachine_graph {n : ℕ} (G : Arcs (Fin n)) (depth : ℕ)
    (source next target : Fin n) :
    let code := steinerHopTransferCode G (source,next)
    let prior := steinerDistanceHopRounds G depth (next,target)
    let input := encodeSteinerUnaryHopTransferCandidate (n+1,code,prior)
    TM2OutputsInTime steinerUnaryHopTransferCandidateMachine input
      (some (encodeSteinerUnaryRoundTotal (steinerHopTransferCandidate n code prior))) (2*input.length) :=
  steinerUnaryHopTransferCandidateMachine_run (n+1) (steinerHopTransferCode G (source,next))
    (steinerDistanceHopRounds G depth (next,target))

end OnlineReachabilityPreservers
