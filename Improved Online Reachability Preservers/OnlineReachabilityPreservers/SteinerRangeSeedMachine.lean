import OnlineReachabilityPreservers.SteinerBinaryRangeMachine
import OnlineReachabilityPreservers.SteinerSeedTapeMachine
import OnlineReachabilityPreservers.SteinerStackTagging

/-! Compose the finite graph range check with the finite seed tape splitter. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

/-- The two input frames use disjoint tags. The output uses the seed
tag on success and begins with a range separator on graph rejection. -/
abbrev SteinerRangeSeedSymbol := Option (Bool × Bool) ⊕ Option Bool

abbrev SteinerRangeSeedRequest := List SteinerRangeWordPair × (ℕ × List Bool)

private abbrev RangeSeedLabel := Option (Fin 4)
private abbrev RangeSeedRegister := (Bool × Bool × Option (Option (Bool × Bool))) × Option (Option Bool)
private abbrev RangeSeedProgram :=
  Turing.TM2.Stmt (fun _ : Fin 3 => SteinerRangeSeedSymbol) RangeSeedLabel RangeSeedRegister

private def rangeSeedRegister (accepted borrow : Bool) : RangeSeedRegister :=
  ((accepted,borrow,none),none)

private def readRangeSymbol : SteinerRangeSeedSymbol → Option (Option (Bool × Bool))
  | .inl range => some range
  | .inr _ => none

private def readSeedSymbol : SteinerRangeSeedSymbol → Option (Option Bool)
  | .inl _ => none
  | .inr seed => some seed

private def seedTag : StackMachineTag (Option Bool) SteinerRangeSeedSymbol (Fin 4)
    RangeSeedLabel (Option (Option Bool)) RangeSeedRegister where
  writeSymbol := Sum.inr
  readSymbol := readSeedSymbol
  writeRegister r := ((true,false,none),r)
  readRegister := Prod.snd
  writeLabel := some
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def observeRangeSeed (r : RangeSeedRegister) (symbol : Option SteinerRangeSeedSymbol) : RangeSeedRegister :=
  ((r.1.1,r.1.2.1,symbol.bind readRangeSymbol),none)

private def consumeRangeSeedBit (r : RangeSeedRegister) (_ : Option SteinerRangeSeedSymbol) : RangeSeedRegister :=
  let pair := r.1.2.2.join.getD (false,false)
  rangeSeedRegister r.1.1 (nextBinaryBorrow pair.1 pair.2 r.1.2.1)

private def consumeRangeSeedSeparator (r : RangeSeedRegister) (_ : Option SteinerRangeSeedSymbol) : RangeSeedRegister :=
  rangeSeedRegister (r.1.1 && r.1.2.1) false

private def rangeSeedCheckProgram : RangeSeedProgram :=
  peek 0 observeRangeSeed <|
    branch (fun r => r.1.2.2.isSome)
      (branch (fun r => r.1.2.2.join.isSome)
        (pop 0 consumeRangeSeedBit <| goto (fun _ => none))
        (pop 0 consumeRangeSeedSeparator <| goto (fun _ => none)))
      (branch (fun r => r.1.1)
        (load (fun _ => rangeSeedRegister true false) <| goto (fun _ => some 0))
        (push 0 (fun _ => Sum.inl none) <| load (fun _ => rangeSeedRegister true false) halt))

private def rangeSeedProgram : RangeSeedLabel → RangeSeedProgram
  | none => rangeSeedCheckProgram
  | some l => seedTag.statement (steinerSeedTapeMachine.m l)

/-- Read tagged endpoint checks, then run the seed machine on the
tagged suffix when every comparison passes. On graph rejection,
return a range separator before the untouched seed request. -/
abbrev steinerRangeSeedMachine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 0
  Γ _ := SteinerRangeSeedSymbol
  Λ := RangeSeedLabel
  main := none
  σ := RangeSeedRegister
  initialState := rangeSeedRegister true false
  m := rangeSeedProgram

private def rangeSeedConfig (label : Option RangeSeedLabel) (accepted borrow : Bool)
    (tape : List SteinerRangeSeedSymbol) : steinerRangeSeedMachine.Cfg where
  l := label
  var := rangeSeedRegister accepted borrow
  stk := ![tape,[],[]]

private theorem rangeSeed_update (tape next : List SteinerRangeSeedSymbol) :
    Function.update (![tape,[],[]] : Fin 3 → List SteinerRangeSeedSymbol) 0 next = ![next,[],[]] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem rangeSeed_bit (accepted borrow : Bool) (bits : Bool × Bool) (tape : List SteinerRangeSeedSymbol) :
    steinerRangeSeedMachine.step (rangeSeedConfig (some none) accepted borrow (Sum.inl (some bits)::tape)) =
      some (rangeSeedConfig (some none) accepted (nextBinaryBorrow bits.1 bits.2 borrow) tape) := by
  simp [FinTM2.step,steinerRangeSeedMachine,rangeSeedConfig,Turing.TM2.step,Turing.TM2.stepAux,
    rangeSeedProgram,rangeSeedCheckProgram,observeRangeSeed,readRangeSymbol,consumeRangeSeedBit,rangeSeed_update]
  rfl

private theorem rangeSeed_separator (accepted borrow : Bool) (tape : List SteinerRangeSeedSymbol) :
    steinerRangeSeedMachine.step (rangeSeedConfig (some none) accepted borrow (Sum.inl none::tape)) =
      some (rangeSeedConfig (some none) (accepted && borrow) false tape) := by
  simp [FinTM2.step,steinerRangeSeedMachine,rangeSeedConfig,Turing.TM2.step,Turing.TM2.stepAux,
    rangeSeedProgram,rangeSeedCheckProgram,observeRangeSeed,readRangeSymbol,consumeRangeSeedSeparator,rangeSeed_update]
  rfl

private theorem rangeSeed_finish (accepted : Bool) (seed : List (Option Bool)) :
    steinerRangeSeedMachine.step (rangeSeedConfig (some none) accepted false (seed.map Sum.inr)) =
      some (if accepted then rangeSeedConfig (some (some 0)) true false (seed.map Sum.inr)
        else rangeSeedConfig none true false (Sum.inl none::seed.map Sum.inr)) := by
  cases accepted <;> cases seed <;>
    simp [FinTM2.step,steinerRangeSeedMachine,rangeSeedConfig,Turing.TM2.step,Turing.TM2.stepAux,
      rangeSeedProgram,rangeSeedCheckProgram,observeRangeSeed,readRangeSymbol,rangeSeed_update] <;> rfl

private def rangeSeed_step {a b : steinerRangeSeedMachine.Cfg} (step : steinerRangeSeedMachine.step a = some b) :
    EvalsToInTime steinerRangeSeedMachine.step a (some b) 1 where
  steps := 1
  evals_in_steps := by change steinerRangeSeedMachine.step a = some b; exact step
  steps_le_m := le_rfl

private def rangeSeed_scanDigits (digits : List (Bool × Bool)) (tape : List SteinerRangeSeedSymbol)
    (accepted borrow : Bool) :
    EvalsToInTime steinerRangeSeedMachine.step
      (rangeSeedConfig (some none) accepted borrow (digits.map (fun pair => Sum.inl (some pair)) ++ tape))
      (some (rangeSeedConfig (some none) accepted (foldedBorrow digits borrow) tape)) digits.length := by
  induction digits generalizing borrow with
  | nil => exact EvalsToInTime.refl _ _
  | cons digit digits ih =>
    have first := rangeSeed_step (rangeSeed_bit accepted borrow digit (digits.map (fun pair => Sum.inl (some pair)) ++ tape))
    exact EvalsToInTime.trans _ _ _ _ _ _ first (ih (nextBinaryBorrow digit.1 digit.2 borrow))

private def rangeSeed_scanChecks (checks : List SteinerRangeWordPair) (accepted : Bool)
    (tape : List SteinerRangeSeedSymbol) :
    EvalsToInTime steinerRangeSeedMachine.step
      (rangeSeedConfig (some none) accepted false ((encodeSteinerRangeChecks checks).map Sum.inl ++ tape))
      (some (rangeSeedConfig (some none) (accepted && steinerRangeChecks checks) false tape))
      (encodeSteinerRangeChecks checks).length := by
  induction checks generalizing accepted with
  | nil => simpa [encodeSteinerRangeChecks,steinerRangeChecks] using
      (EvalsToInTime.refl steinerRangeSeedMachine.step (rangeSeedConfig (some none) accepted false tape))
  | cons check rest ih =>
    let digits := alignBinaryDigits check.1 check.2
    let pending := encodeSteinerRangeChecks rest
    let flag := (binaryLessWithWork check.1 check.2 false).1
    let tail := pending.map (Sum.inl : Option (Bool × Bool) → SteinerRangeSeedSymbol) ++ tape
    have scan := rangeSeed_scanDigits digits (Sum.inl none::tail) accepted false
    rw [show foldedBorrow digits false = flag from alignedBorrow_eq_binaryLess _ _ _] at scan
    have divider := rangeSeed_step (rangeSeed_separator accepted flag tail)
    have first := EvalsToInTime.trans _ _ _ _ _ _ scan divider
    have later := ih (accepted && flag)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first later
    have length : (encodeSteinerRangeChecks (check::rest)).length = pending.length+(1+digits.length) := by
      change ((digits.map some ++ [none]) ++ pending).length = _
      simp only [List.length_append,List.length_map,List.length_singleton]
      omega
    rw [length]
    simpa only [encodeSteinerRangeChecks,List.flatMap_cons,List.map_append,List.map_map,Function.comp_def,
      List.map_cons,List.map_nil,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,
      steinerRangeChecks,List.all_cons,
      Bool.and_assoc,digits,tail,pending,flag] using all

private theorem rangeSeed_init (tape : List SteinerRangeSeedSymbol) :
    initList steinerRangeSeedMachine tape = rangeSeedConfig (some none) true false tape := by
  unfold initList rangeSeedConfig
  apply congrArg (fun stk : Fin 3 → List SteinerRangeSeedSymbol =>
    (⟨some none,rangeSeedRegister true false,stk⟩ : steinerRangeSeedMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem rangeSeed_halt (output : List SteinerRangeSeedSymbol) :
    haltList steinerRangeSeedMachine output = rangeSeedConfig none true false output := by
  unfold haltList rangeSeedConfig
  apply congrArg (fun stk : Fin 3 → List SteinerRangeSeedSymbol =>
    (⟨none,rangeSeedRegister true false,stk⟩ : steinerRangeSeedMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem rangeSeed_tag_init (seed : List (Option Bool)) :
    seedTag.configuration (initList steinerSeedTapeMachine seed) =
      rangeSeedConfig (some (some 0)) true false (seed.map Sum.inr) := by
  apply congrArg (fun stk : Fin 3 → List SteinerRangeSeedSymbol =>
    (⟨some (some 0),rangeSeedRegister true false,stk⟩ : steinerRangeSeedMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem rangeSeed_tag_halt (out : List (Option Bool)) :
    seedTag.configuration (haltList steinerSeedTapeMachine out) =
      rangeSeedConfig none true false (out.map Sum.inr) := by
  apply congrArg (fun stk : Fin 3 → List SteinerRangeSeedSymbol =>
    (⟨none,rangeSeedRegister true false,stk⟩ : steinerRangeSeedMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- Concatenate the tagged range encodings and the tagged unary count
and finite bit tape. The tags mark the boundary without an extra symbol. -/
def encodeSteinerRangeSeed (request : SteinerRangeSeedRequest) : List SteinerRangeSeedSymbol :=
  (encodeSteinerRangeChecks request.1).map Sum.inl ++ (encodeSteinerSeedTapeRequest request.2).map Sum.inr

/-- Interpret an accepted seed output, or preserve the complete seed
request after a rejection marker when the graph check fails. -/
def encodeSteinerRangeSeedAnswer (accepted : Bool) (seedRequest seedOutput : List (Option Bool)) :
    List SteinerRangeSeedSymbol :=
  if accepted then seedOutput.map Sum.inr else Sum.inl none::seedRequest.map Sum.inr

def steinerRangeSeedAnswer (request : SteinerRangeSeedRequest) : List SteinerRangeSeedSymbol :=
  encodeSteinerRangeSeedAnswer (steinerRangeChecks request.1)
    (encodeSteinerSeedTapeRequest request.2) (splitSteinerSeedTapeOrReject request.2)

private def rangeSeed_execute (checks : List SteinerRangeWordPair) (seed out : List (Option Bool))
    (bound : ℕ) (certified : TM2OutputsInTime steinerSeedTapeMachine seed (some out) bound) :
    EvalsToInTime steinerRangeSeedMachine.step
      (rangeSeedConfig (some none) true false ((encodeSteinerRangeChecks checks).map Sum.inl ++ seed.map Sum.inr))
      (some (rangeSeedConfig none true false (encodeSteinerRangeSeedAnswer (steinerRangeChecks checks) seed out)))
      ((encodeSteinerRangeChecks checks).length+bound+1) := by
  have scan := rangeSeed_scanChecks checks true (seed.map Sum.inr)
  cases accepted : steinerRangeChecks checks <;> simp only [accepted,Bool.true_and] at scan
  · have finish := rangeSeed_step (rangeSeed_finish false seed)
    have all := EvalsToInTime.trans _ _ _ _ _ _ scan finish
    simpa only [encodeSteinerRangeSeedAnswer,Bool.false_eq_true,↓reduceIte] using
      (show EvalsToInTime steinerRangeSeedMachine.step _ _
        ((encodeSteinerRangeChecks checks).length+bound+1) from
      ⟨all.toEvalsTo, by have h := all.steps_le_m; omega⟩)
  · have finish := rangeSeed_step (rangeSeed_finish true seed)
    have before := EvalsToInTime.trans _ _ _ _ _ _ scan finish
    have continued := seedTag.evaluation (host := rangeSeedProgram) (base := steinerSeedTapeMachine.m)
      (fun _ => rfl) certified
    change EvalsToInTime steinerRangeSeedMachine.step (seedTag.configuration (initList steinerSeedTapeMachine seed))
      (some (seedTag.configuration (haltList steinerSeedTapeMachine out))) bound at continued
    rw [rangeSeed_tag_init,rangeSeed_tag_halt] at continued
    have all := EvalsToInTime.trans _ _ _ _ _ _ before continued
    simpa only [encodeSteinerRangeSeedAnswer,↓reduceIte] using
      (show EvalsToInTime steinerRangeSeedMachine.step _ _
        ((encodeSteinerRangeChecks checks).length+bound+1) from
      ⟨all.toEvalsTo, by have h := all.steps_le_m; omega⟩)

/-- The composed machine returns the exact guarded seed result for
every supplied range batch, count, and finite tape. -/
def steinerRangeSeedMachine_run (request : SteinerRangeSeedRequest) :
    TM2OutputsInTime steinerRangeSeedMachine (encodeSteinerRangeSeed request)
      (some (steinerRangeSeedAnswer request))
      ((encodeSteinerRangeChecks request.1).length+3*request.2.1+4) := by
  have all := rangeSeed_execute request.1 (encodeSteinerSeedTapeRequest request.2)
    (splitSteinerSeedTapeOrReject request.2) _ (steinerSeedTapeMachine_runOrReject request.2)
  change EvalsToInTime steinerRangeSeedMachine.step _
    (some (haltList steinerRangeSeedMachine _)) _
  rw [rangeSeed_init,rangeSeed_halt]
  exact ⟨all.toEvalsTo,by have h := all.steps_le_m; omega⟩

/-- Linear time in the supplied concatenated encoding, including rejection
by the range check and exhaustion in the seed phase. -/
noncomputable def steinerRangeSeedMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerRangeSeed id steinerRangeSeedAnswer where
  tm := steinerRangeSeedMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 3*Polynomial.X+Polynomial.C 4
  outputsFun request := by
    have run := steinerRangeSeedMachine_run request
    have length : (encodeSteinerRangeSeed request).length =
        (encodeSteinerRangeChecks request.1).length+request.2.1+request.2.2.length := by
      simp [encodeSteinerRangeSeed,encodeSteinerSeedTapeRequest,Nat.add_assoc]
    have enlarged : (encodeSteinerRangeChecks request.1).length+3*request.2.1+4 ≤
        (Polynomial.C 3*Polynomial.X+Polynomial.C 4).eval (encodeSteinerRangeSeed request).length := by
      simp only [Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_X,Polynomial.eval_C,length]
      omega
    change TM2OutputsInTime steinerRangeSeedMachine ((encodeSteinerRangeSeed request).map id)
      (some ((steinerRangeSeedAnswer request).map id)) _
    simpa only [List.map_id_fun,id_eq] using
      (show TM2OutputsInTime steinerRangeSeedMachine (encodeSteinerRangeSeed request)
        (some (steinerRangeSeedAnswer request)) _ from ⟨run.toEvalsTo,run.steps_le_m.trans enlarged⟩)

/-- On graph rows, use the guarded decoder's acceptance flag at the
actual variable-word input width. An accepted graph invokes the
finite sampler with the supplied count. Its seed and remainder are
encoded by the seed machine, with the empty output for exhaustion. -/
def steinerRangeSeedMachine_guardedSampler {n size : ℕ} (bound : List Bool)
    (number : binaryWordValue bound = n) (rows : List SteinerRangeWordPair)
    (count : {b : ℕ // b = size}) (tape : List Bool) :
    TM2OutputsInTime steinerRangeSeedMachine
      (encodeSteinerRangeSeed (steinerRangeRequests bound rows,(size,tape)))
      (some (encodeSteinerRangeSeedAnswer
        ((decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1.isSome)
        (encodeSteinerSeedTapeRequest (size,tape))
        ((((readSteinerSeedWithWork count steinerBitTapeSource).run tape).map encodeSavedSteinerSeed).getD [])))
      (binaryEndpointBits rows+2*rows.length*(bound.length+1)+3*size+4) := by
  have checked : (decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1 =
      (decodeBinaryFinArcRowsWithWork (n := n) 0 rows).1 := by
    ext decoded
    exact decodeCheckedBinaryFinArcRowsWithWork_of_actual_bits rows decoded
  have flag : steinerRangeChecks (steinerRangeRequests bound rows) =
      (decodeBinaryFinArcRowsWithWork (n := n) 0 rows).1.isSome := by
    apply Bool.eq_iff_iff.mpr
    exact (steinerRangeRequests_accepts_iff bound number rows 0).trans Option.isSome_iff_exists.symm
  have seed := steinerSeedTapeMachine_refinesFiniteSampler count tape
  have all := rangeSeed_execute (steinerRangeRequests bound rows) (encodeSteinerSeedTapeRequest (size,tape)) _ _ seed
  have boundLen := encodeSteinerRangeRequests_length_le bound rows
  change EvalsToInTime steinerRangeSeedMachine.step _
    (some (haltList steinerRangeSeedMachine _)) _
  rw [rangeSeed_init,rangeSeed_halt,checked,← flag]
  exact ⟨all.toEvalsTo,by have h := all.steps_le_m; omega⟩

/-- A failed graph check returns the untouched seed frame and never
invokes the seed routine. Its bound is independent of the seed length. -/
def steinerRangeSeedMachine_rejectedGraph (request : SteinerRangeSeedRequest)
    (rejected : steinerRangeChecks request.1 = false) :
    TM2OutputsInTime steinerRangeSeedMachine (encodeSteinerRangeSeed request)
      (some (Sum.inl none::(encodeSteinerSeedTapeRequest request.2).map Sum.inr))
      ((encodeSteinerRangeChecks request.1).length+1) := by
  let seed := encodeSteinerSeedTapeRequest request.2
  have scan := rangeSeed_scanChecks request.1 true (seed.map Sum.inr)
  simp only [rejected,Bool.true_and] at scan
  have finish := rangeSeed_step (rangeSeed_finish false seed)
  have all := EvalsToInTime.trans _ _ _ _ _ _ scan finish
  change EvalsToInTime steinerRangeSeedMachine.step _
    (some (haltList steinerRangeSeedMachine _)) _
  rw [rangeSeed_init,rangeSeed_halt]
  exact ⟨all.toEvalsTo,by have h := all.steps_le_m; omega⟩

end OnlineReachabilityPreservers
