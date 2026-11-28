import OnlineReachabilityPreservers.SteinerDistanceHopRounds
import OnlineReachabilityPreservers.SteinerUnaryRoundTotalMachine

/-! Fold a list of unary candidates into their minimum with an initial value. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev MinimumSymbol := SteinerUnaryCappedRowsSymbol
private abbrev MinimumRegister := Option MinimumSymbol

private inductive MinimumLabel where
  | first
  | scan (side : Bool)
  | clear (side : Bool)
  | finish (side : Bool)
  deriving Fintype

private abbrev MinimumProgram := StackMachineTag.Program (Fin 4) MinimumSymbol MinimumLabel MinimumRegister

private def minimumTally : MinimumSymbol := Sum.inr (some true)
private def minimumField : MinimumSymbol := Sum.inr none
private abbrev minimumTallies := encodeSteinerUnaryRoundTotal

private def minimumIsTally : MinimumRegister → Bool
  | some (.inr (some true)) => true
  | _ => false

private def minimumBuffer : Bool → Fin 4
  | false => 1
  | true => 2

private def minimumPop (slot : Fin 4) (next : MinimumProgram) : MinimumProgram :=
  pop slot (fun _ seen => seen) next

private def minimumPush (slot : Fin 4) (next : MinimumProgram) : MinimumProgram :=
  push slot (fun _ => minimumTally) next

private def minimumGoto (label : MinimumLabel) : MinimumProgram :=
  load (fun _ => none) (goto fun _ => label)

private def minimumProgram : MinimumLabel → MinimumProgram
  | .first => minimumPop 0 <| branch minimumIsTally
      (minimumPush 1 (minimumGoto .first)) (minimumGoto (.scan false))
  | .scan side => minimumPop 0 <| branch Option.isSome
      (branch minimumIsTally
        (minimumPop (minimumBuffer side) <| branch Option.isSome
          (minimumPush (minimumBuffer (!side)) (minimumGoto (.scan side))) (minimumGoto (.scan side)))
        (minimumGoto (.clear side)))
      (minimumGoto (.finish side))
  | .clear side => minimumPop (minimumBuffer side) <| branch Option.isSome
      (minimumGoto (.clear side)) (minimumGoto (.scan (!side)))
  | .finish side => minimumPop (minimumBuffer side) <| branch Option.isSome
      (minimumPush 3 (minimumGoto (.finish side))) (load (fun _ => none) halt)

/-- Match unary tallies between the minimum so far and each new field.
The matched tallies become the minimum on the other buffer. -/
abbrev steinerUnaryMinimumMachine : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 3
  Γ _ := MinimumSymbol
  Λ := MinimumLabel
  main := .first
  σ := MinimumRegister
  initialState := none
  m := minimumProgram

private def minimumTapes (word : List MinimumSymbol) (a b out : ℕ) : Fin 4 → List MinimumSymbol :=
  ![word,minimumTallies a,minimumTallies b,minimumTallies out]

private def minimumCfg (label : Option MinimumLabel) (word : List MinimumSymbol) (a b out : ℕ) :
    steinerUnaryMinimumMachine.Cfg :=
  ⟨label,none,minimumTapes word a b out⟩

private def minimumSideCfg (label : Option MinimumLabel) : Bool → List MinimumSymbol →
    ℕ → ℕ → ℕ → steinerUnaryMinimumMachine.Cfg
  | false,word,current,spare,out => minimumCfg label word current spare out
  | true,word,current,spare,out => minimumCfg label word spare current out

private theorem minimumTallies_succ (n : ℕ) : minimumTallies (n+1) = minimumTally::minimumTallies n := rfl

private theorem minimum_update0 (word new : List MinimumSymbol) (a b out : ℕ) :
    Function.update (minimumTapes word a b out) 0 new = minimumTapes new a b out := by
  funext i
  fin_cases i <;> simp [minimumTapes,Function.update]

private theorem minimum_update1 (word : List MinimumSymbol) (a b out n : ℕ) :
    Function.update (minimumTapes word a b out) 1 (minimumTallies n) = minimumTapes word n b out := by
  funext i
  fin_cases i <;> simp [minimumTapes,Function.update]

private theorem minimum_update2 (word : List MinimumSymbol) (a b out n : ℕ) :
    Function.update (minimumTapes word a b out) 2 (minimumTallies n) = minimumTapes word a n out := by
  funext i
  fin_cases i <;> simp [minimumTapes,Function.update]

private theorem minimum_update3 (word : List MinimumSymbol) (a b out n : ℕ) :
    Function.update (minimumTapes word a b out) 3 (minimumTallies n) = minimumTapes word a b n := by
  funext i
  fin_cases i <;> simp [minimumTapes,Function.update]

private abbrev MinimumRun (before after : steinerUnaryMinimumMachine.Cfg) (time : ℕ) :=
  EvalsToInTime steinerUnaryMinimumMachine.step before (some after) time

private def minimumOne {a b : steinerUnaryMinimumMachine.Cfg}
    (move : steinerUnaryMinimumMachine.step a = some b) : MinimumRun a b 1 := ⟨⟨1,move⟩,le_rfl⟩

private def minimumThen {a b c : steinerUnaryMinimumMachine.Cfg} {x y : ℕ}
    (first : MinimumRun a b x) (next : MinimumRun b c y) : MinimumRun a c (x+y) := by
  simpa only [Nat.add_comm] using EvalsToInTime.trans _ _ _ _ _ _ first next

private def minimumRelax {a b : steinerUnaryMinimumMachine.Cfg} {x y : ℕ}
    (run : MinimumRun a b x) (le : x ≤ y) : MinimumRun a b y := ⟨run.toEvalsTo,run.steps_le_m.trans le⟩

private theorem minimumFirst_more (word : List MinimumSymbol) (current : ℕ) :
    steinerUnaryMinimumMachine.step (minimumCfg (some .first) (minimumTally::word) current 0 0) =
      some (minimumCfg (some .first) word (current+1) 0 0) := by
  simp only [FinTM2.step,steinerUnaryMinimumMachine,minimumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    minimumProgram,minimumPop,minimumPush,minimumGoto,minimum_update0]
  change some (⟨some .first,none,Function.update (minimumTapes word current 0 0) 1 (minimumTallies (current+1))⟩ : steinerUnaryMinimumMachine.Cfg) = _
  rw [minimum_update1]
  rfl

private theorem minimumFirst_end (word : List MinimumSymbol) (current : ℕ) :
    steinerUnaryMinimumMachine.step (minimumCfg (some .first) (minimumField::word) current 0 0) =
      some (minimumCfg (some (.scan false)) word current 0 0) := by
  simp only [FinTM2.step,steinerUnaryMinimumMachine,minimumCfg,Turing.TM2.step,Turing.TM2.stepAux,
    minimumProgram,minimumPop,minimumPush,minimumGoto,minimum_update0]
  rfl

private def minimumFirstRun (count : ℕ) (word : List MinimumSymbol) (current : ℕ) :
    MinimumRun (minimumCfg (some .first) (minimumTallies count++minimumField::word) current 0 0)
      (minimumCfg (some (.scan false)) word (current+count) 0 0) (count+1) := by
  induction count generalizing current with
  | zero => exact minimumOne (minimumFirst_end word current)
  | succ count ih =>
    have run := minimumThen (minimumOne (minimumFirst_more _ current)) (ih (current+1))
    simpa only [minimumTallies_succ,List.cons_append,Nat.add_right_comm,Nat.add_assoc,Nat.add_left_comm] using run

private theorem minimumScan_zero (side : Bool) (word : List MinimumSymbol) (spare : ℕ) :
    steinerUnaryMinimumMachine.step (minimumSideCfg (some (.scan side)) side (minimumTally::word) 0 spare 0) =
      some (minimumSideCfg (some (.scan side)) side word 0 spare 0) := by
  cases side <;> simp only [minimumSideCfg,FinTM2.step,steinerUnaryMinimumMachine,minimumCfg,Turing.TM2.step,
    Turing.TM2.stepAux,minimumProgram,minimumPop,minimumPush,minimumGoto,minimumBuffer,minimum_update0]
  · change some (⟨some _,none,Function.update _ 1 (minimumTallies 0)⟩ : steinerUnaryMinimumMachine.Cfg) = _
    rw [minimum_update1]
    rfl
  · change some (⟨some _,none,Function.update _ 2 (minimumTallies 0)⟩ : steinerUnaryMinimumMachine.Cfg) = _
    rw [minimum_update2]
    rfl

private theorem minimumScan_more (side : Bool) (word : List MinimumSymbol) (current spare : ℕ) :
    steinerUnaryMinimumMachine.step (minimumSideCfg (some (.scan side)) side (minimumTally::word) (current+1) spare 0) =
      some (minimumSideCfg (some (.scan side)) side word current (spare+1) 0) := by
  cases side <;> simp only [minimumSideCfg,FinTM2.step,steinerUnaryMinimumMachine,minimumCfg,Turing.TM2.step,
    Turing.TM2.stepAux,minimumProgram,minimumPop,minimumPush,minimumGoto,minimumBuffer,minimum_update0]
  · change some (⟨some _,none,Function.update (Function.update (minimumTapes word (current+1) spare 0) 1
        (minimumTallies current)) 2 (minimumTallies (spare+1))⟩ : steinerUnaryMinimumMachine.Cfg) = _
    rw [minimum_update1,minimum_update2]
    rfl
  · change some (⟨some _,none,Function.update (Function.update (minimumTapes word spare (current+1) 0) 2
        (minimumTallies current)) 1 (minimumTallies (spare+1))⟩ : steinerUnaryMinimumMachine.Cfg) = _
    rw [minimum_update2,minimum_update1]
    rfl

private def minimumScanTallies (side : Bool) (value : ℕ) (word : List MinimumSymbol) (current spare : ℕ) :
    MinimumRun (minimumSideCfg (some (.scan side)) side (minimumTallies value++word) current spare 0)
      (minimumSideCfg (some (.scan side)) side word (current-value) (spare+min current value) 0) value := by
  induction value generalizing current spare with
  | zero =>
    simp only [Nat.sub_zero,Nat.min_zero,Nat.add_zero]
    exact ⟨⟨0,rfl⟩,le_rfl⟩
  | succ value ih =>
    cases current with
    | zero =>
      have run := minimumThen (minimumOne (minimumScan_zero side _ spare)) (ih 0 spare)
      simpa only [minimumTallies_succ,List.cons_append,Nat.zero_sub,Nat.zero_min,Nat.add_zero,Nat.add_comm 1] using run
    | succ current =>
      have run := minimumThen (minimumOne (minimumScan_more side _ current spare)) (ih current (spare+1))
      have minimum : min (current+1) (value+1) = min current value+1 := by omega
      simpa only [minimumTallies_succ,List.cons_append,Nat.succ_sub_succ_eq_sub,minimum,Nat.add_assoc,
        Nat.add_comm 1] using run

private theorem minimumScan_field (side : Bool) (word : List MinimumSymbol) (current spare : ℕ) :
    steinerUnaryMinimumMachine.step (minimumSideCfg (some (.scan side)) side (minimumField::word) current spare 0) =
      some (minimumSideCfg (some (.clear side)) side word current spare 0) := by
  cases side <;> simp only [minimumSideCfg,FinTM2.step,steinerUnaryMinimumMachine,minimumCfg,Turing.TM2.step,
    Turing.TM2.stepAux,minimumProgram,minimumPop,minimumGoto,minimum_update0] <;> rfl

private theorem minimumScan_end (side : Bool) (current : ℕ) :
    steinerUnaryMinimumMachine.step (minimumSideCfg (some (.scan side)) side [] current 0 0) =
      some (minimumSideCfg (some (.finish side)) side [] current 0 0) := by
  cases side <;> simp only [minimumSideCfg,FinTM2.step,steinerUnaryMinimumMachine,minimumCfg,Turing.TM2.step,
    Turing.TM2.stepAux,minimumProgram,minimumPop,minimumGoto,minimum_update0] <;> rfl

private theorem minimumClear_more (side : Bool) (word : List MinimumSymbol) (current spare : ℕ) :
    steinerUnaryMinimumMachine.step (minimumSideCfg (some (.clear side)) side word (current+1) spare 0) =
      some (minimumSideCfg (some (.clear side)) side word current spare 0) := by
  cases side <;> simp only [minimumSideCfg,FinTM2.step,steinerUnaryMinimumMachine,minimumCfg,Turing.TM2.step,
    Turing.TM2.stepAux,minimumProgram,minimumPop,minimumGoto,minimumBuffer]
  · change some (⟨some _,none,Function.update _ 1 (minimumTallies current)⟩ : steinerUnaryMinimumMachine.Cfg) = _
    rw [minimum_update1]
    rfl
  · change some (⟨some _,none,Function.update _ 2 (minimumTallies current)⟩ : steinerUnaryMinimumMachine.Cfg) = _
    rw [minimum_update2]
    rfl

private theorem minimumClear_end (side : Bool) (word : List MinimumSymbol) (spare : ℕ) :
    steinerUnaryMinimumMachine.step (minimumSideCfg (some (.clear side)) side word 0 spare 0) =
      some (minimumSideCfg (some (.scan (!side))) (!side) word spare 0 0) := by
  cases side <;> simp only [minimumSideCfg,FinTM2.step,steinerUnaryMinimumMachine,minimumCfg,Turing.TM2.step,
    Turing.TM2.stepAux,minimumProgram,minimumPop,minimumGoto,minimumBuffer]
  · change some (⟨some _,none,Function.update _ 1 (minimumTallies 0)⟩ : steinerUnaryMinimumMachine.Cfg) = _
    rw [minimum_update1]
    rfl
  · change some (⟨some _,none,Function.update _ 2 (minimumTallies 0)⟩ : steinerUnaryMinimumMachine.Cfg) = _
    rw [minimum_update2]
    rfl

private def minimumClear (side : Bool) (word : List MinimumSymbol) (current spare : ℕ) :
    MinimumRun (minimumSideCfg (some (.clear side)) side word current spare 0)
      (minimumSideCfg (some (.scan (!side))) (!side) word spare 0 0) (current+1) := by
  induction current with
  | zero => exact minimumOne (minimumClear_end side word spare)
  | succ current ih =>
    have run := minimumThen (minimumOne (minimumClear_more side word current spare)) ih
    exact minimumRelax run (by omega)

private theorem minimumFinish_more (side : Bool) (current out : ℕ) :
    steinerUnaryMinimumMachine.step (minimumSideCfg (some (.finish side)) side [] (current+1) 0 out) =
      some (minimumSideCfg (some (.finish side)) side [] current 0 (out+1)) := by
  cases side <;> simp only [minimumSideCfg,FinTM2.step,steinerUnaryMinimumMachine,minimumCfg,Turing.TM2.step,
    Turing.TM2.stepAux,minimumProgram,minimumPop,minimumPush,minimumGoto,minimumBuffer]
  · change some (⟨some _,none,Function.update (Function.update _ 1 (minimumTallies current)) 3
        (minimumTallies (out+1))⟩ : steinerUnaryMinimumMachine.Cfg) = _
    rw [minimum_update1,minimum_update3]
    rfl
  · change some (⟨some _,none,Function.update (Function.update _ 2 (minimumTallies current)) 3
        (minimumTallies (out+1))⟩ : steinerUnaryMinimumMachine.Cfg) = _
    rw [minimum_update2,minimum_update3]
    rfl

private theorem minimumFinish_end (side : Bool) (out : ℕ) :
    steinerUnaryMinimumMachine.step (minimumSideCfg (some (.finish side)) side [] 0 0 out) =
      some (minimumCfg none [] 0 0 out) := by
  cases side <;> simp only [minimumSideCfg,FinTM2.step,steinerUnaryMinimumMachine,minimumCfg,Turing.TM2.step,
    Turing.TM2.stepAux,minimumProgram,minimumPop,minimumBuffer]
  · change some (⟨none,none,Function.update _ 1 (minimumTallies 0)⟩ : steinerUnaryMinimumMachine.Cfg) = _
    rw [minimum_update1]
    rfl
  · change some (⟨none,none,Function.update _ 2 (minimumTallies 0)⟩ : steinerUnaryMinimumMachine.Cfg) = _
    rw [minimum_update2]
    rfl

private def minimumFinish (side : Bool) (current out : ℕ) :
    MinimumRun (minimumSideCfg (some (.finish side)) side [] current 0 out)
      (minimumCfg none [] 0 0 (out+current)) (current+1) := by
  induction current generalizing out with
  | zero => exact minimumOne (minimumFinish_end side out)
  | succ current ih =>
    have run := minimumThen (minimumOne (minimumFinish_more side current out)) (ih (out+1))
    simpa only [Nat.add_right_comm,Nat.add_assoc,Nat.add_left_comm] using run

private theorem minimumFrame_cons (value : ℕ) (tail : List ℕ) :
    encodeSteinerUnaryRoundPriorVector (value::tail) =
      minimumTallies value++minimumField::encodeSteinerUnaryRoundPriorVector tail := by
  change (minimumTallies value++[minimumField])++encodeSteinerUnaryRoundPriorVector tail = _
  rw [List.append_assoc,List.singleton_append]

private def minimumCandidates (side : Bool) (values : List ℕ) (current : ℕ) :
    let fields := encodeSteinerUnaryRoundPriorVector values
    MinimumRun (minimumSideCfg (some (.scan side)) side fields current 0 0)
      (minimumCfg none [] 0 0 (values.foldl min current)) (2*fields.length+current+2) := by
  induction values generalizing side current with
  | nil =>
    have run := minimumThen (minimumOne (minimumScan_end side current)) (minimumFinish side current 0)
    simp only [Nat.zero_add] at run
    simp only [encodeSteinerUnaryRoundPriorVector,List.flatMap_nil,List.length_nil,List.foldl_nil,Nat.mul_zero,Nat.zero_add]
    exact minimumRelax run (by omega)
  | cons value tail ih =>
    dsimp only
    rw [minimumFrame_cons]
    let fields := encodeSteinerUnaryRoundPriorVector tail
    let matched := min current value
    let left := current-value
    have scan := minimumScanTallies side value (minimumField::fields) current 0
    simp only [Nat.zero_add] at scan
    have mark := minimumOne (minimumScan_field side fields left matched)
    have erase := minimumClear side fields left matched
    have next := ih (!side) matched
    change MinimumRun _ _ (2*fields.length+matched+2) at next
    have run := minimumThen (minimumThen (minimumThen scan mark) erase) next
    refine minimumRelax run ?_
    change _ ≤ 2*(minimumTallies value++minimumField::fields).length+current+2
    simp only [List.length_append,List.length_cons,encodeSteinerUnaryRoundTotal,List.length_replicate]
    dsimp only [left,matched]
    omega

/-- The old value is the first field and supplies the default minimum
when the list of new candidates is empty. -/
def encodeSteinerUnaryMinimum (request : ℕ × List ℕ) : List SteinerUnaryCappedRowsSymbol :=
  encodeSteinerUnaryRoundPriorVector (request.1::request.2)

private theorem minimumInit (word : List MinimumSymbol) :
    initList steinerUnaryMinimumMachine word = minimumCfg (some .first) word 0 0 0 := by
  apply congrArg (fun tapes : Fin 4 → List MinimumSymbol =>
    (⟨some .first,none,tapes⟩ : steinerUnaryMinimumMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem minimumHalt (out : ℕ) :
    haltList steinerUnaryMinimumMachine (encodeSteinerUnaryRoundTotal out) = minimumCfg none [] 0 0 out := by
  apply congrArg (fun tapes : Fin 4 → List MinimumSymbol =>
    (⟨none,none,tapes⟩ : steinerUnaryMinimumMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- The actual minimum computation uses at most two transitions per
encoded symbol plus one. -/
def steinerUnaryMinimumMachine_run (request : ℕ × List ℕ) :
    let input := encodeSteinerUnaryMinimum request
    TM2OutputsInTime steinerUnaryMinimumMachine input
      (some (encodeSteinerUnaryRoundTotal (request.2.foldl min request.1))) (2*input.length+1) := by
  let fields := encodeSteinerUnaryRoundPriorVector request.2
  have prefixRun := minimumFirstRun request.1 fields 0
  simp only [Nat.zero_add] at prefixRun
  have rest := minimumCandidates false request.2 request.1
  have run := minimumThen prefixRun rest
  change MinimumRun (initList steinerUnaryMinimumMachine (encodeSteinerUnaryMinimum request))
    (haltList steinerUnaryMinimumMachine _) _
  rw [minimumInit,minimumHalt,encodeSteinerUnaryMinimum,minimumFrame_cons]
  refine minimumRelax run ?_
  simp only [List.length_append,List.length_cons,encodeSteinerUnaryRoundTotal,List.length_replicate]
  change request.1+1+(2*fields.length+request.1+2) ≤ 2*(request.1+(fields.length+1))+1
  omega

/-- Linear native running time on the supplied unary fields. -/
noncomputable def steinerUnaryMinimumMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryMinimum encodeSteinerUnaryRoundTotal
      (fun request => request.2.foldl min request.1) where
  tm := steinerUnaryMinimumMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2*Polynomial.X+Polynomial.C 1
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_X,
      Polynomial.eval_C] using steinerUnaryMinimumMachine_run request

section HopCell

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- The old entry and one candidate for each potential successor. -/
def steinerDistanceHopMinimumRequest (G : Arcs V) (depth : ℕ) (d : V × V) : ℕ × List ℕ :=
  let previous := steinerDistanceHopRounds G depth
  (previous d,steinerDistanceHopCandidates G previous d.1 d.2)

/-- A prepared cell needs n+1 fields, each with at most n+2 tallies. -/
theorem encodeSteinerDistanceHopMinimumRequest_length_le (G : Arcs V) (depth : ℕ) (d : V × V) :
    (encodeSteinerUnaryMinimum (steinerDistanceHopMinimumRequest G depth d)).length ≤
      (Fintype.card V+1)*(Fintype.card V+3) := by
  let request := steinerDistanceHopMinimumRequest G depth d
  let values := request.1::request.2
  let packed : Vector ℕ values.length := ⟨values.toArray,by simp⟩
  have same : packed.toList = values := by simp [packed,Vector.toList]
  have count : values.length = Fintype.card V+1 := by
    simp only [values,request,steinerDistanceHopMinimumRequest,List.length_cons,steinerDistanceHopCandidates_length]
  have old := steinerDistanceHopRounds_cap G depth d
  have bounded (value : ℕ) (member : value ∈ values) : value ≤ Fintype.card V+2 := by
    rcases List.mem_cons.mp member with equal | candidate
    · change request.1 ≤ Fintype.card V+1 at old
      omega
    · change value ∈ steinerDistanceHopCandidates G (steinerDistanceHopRounds G depth) d.1 d.2 at candidate
      unfold steinerDistanceHopCandidates at candidate
      obtain ⟨next,_,rfl⟩ := List.mem_map.mp candidate
      split_ifs
      · have cap := steinerDistanceHopRounds_cap G depth (next,d.2)
        omega
      · omega
  have packedBound (i : Fin values.length) : packed[i.val] ≤ Fintype.card V+2 := by
    let value := packed[i.val]
    have on : value ∈ packed.toList := Vector.mem_toList_iff.mpr (Vector.getElem_mem i.isLt)
    exact bounded value ((congrArg (fun row => value ∈ row) same).mp on)
  have encoded := encodeSteinerUnaryRoundPriorVector_length_le packed packedBound
  rw [same,count] at encoded
  exact encoded

/-- Evaluate one exact next hop entry from its supplied unary fields. -/
def steinerUnaryMinimumMachine_hopCell (G : Arcs V) (depth : ℕ) (d : V × V) :
    TM2OutputsInTime steinerUnaryMinimumMachine
      (encodeSteinerUnaryMinimum (steinerDistanceHopMinimumRequest G depth d))
      (some (encodeSteinerUnaryRoundTotal (steinerDistanceHopRounds G (depth+1) d)))
      (2*((Fintype.card V+1)*(Fintype.card V+3))+1) := by
  let run := steinerUnaryMinimumMachine_run (steinerDistanceHopMinimumRequest G depth d)
  have length := encodeSteinerDistanceHopMinimumRequest_length_le G depth d
  exact ⟨run.toEvalsTo,run.steps_le_m.trans (by omega)⟩

end HopCell

end OnlineReachabilityPreservers
