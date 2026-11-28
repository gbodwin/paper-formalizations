import Mathlib.Computability.TuringMachine.Computable
import OnlineReachabilityPreservers.SteinerBinarySeedTape

/-! A finite stack machine for the Steiner seed prefix and tape exhaustion. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev SeedTapeSymbol := Option Bool
private abbrev SeedTapeRegister := Option SeedTapeSymbol
private abbrev SeedTapeStmt := Turing.TM2.Stmt (fun _ : Fin 3 => SeedTapeSymbol) (Fin 4) SeedTapeRegister

private def seedTapeMachineProgram (label : Fin 4) : SeedTapeStmt :=
  if label = 0 then
    peek 0 (fun _ symbol => symbol) <|
      branch (· == some none)
        (pop 0 (fun _ _ => none) <| push 1 (fun _ => none) <| goto (fun _ => 0))
        (load (fun _ => none) <| goto (fun _ => 1))
  else if label = 1 then
    peek 1 (fun _ symbol => symbol) <|
      branch Option.isSome
        (pop 1 (fun _ _ => none) <| pop 0 (fun _ symbol => symbol) <|
          branch Option.isSome
            (push 2 (·.getD none) <| load (fun _ => none) <| goto (fun _ => 1))
            (load (fun _ => none) <| goto (fun _ => 3)))
        (push 0 (fun _ => none) <| load (fun _ => none) <| goto (fun _ => 2))
  else if label = 2 then
    peek 2 (fun _ symbol => symbol) <|
      branch Option.isSome
        (pop 2 (fun _ symbol => symbol) <| push 0 (·.getD none) <|
          load (fun _ => none) <| goto (fun _ => 2))
        (load (fun _ => none) halt)

  else
    peek 1 (fun _ symbol => symbol) <|
      branch Option.isSome
        (pop 1 (fun _ _ => none) <| goto (fun _ => 3))
        (peek 2 (fun _ symbol => symbol) <|
          branch Option.isSome
            (pop 2 (fun _ _ => none) <| goto (fun _ => 3))
            (load (fun _ => none) halt))

/-- Load one marker per requested bit, transfer that prefix, then restore
it before a separator and the untouched suffix on the output stack.
If a bit is missing, clear the work stacks and return the empty output. -/
abbrev steinerSeedTapeMachine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 0
  Γ _ := SeedTapeSymbol
  Λ := Fin 4
  main := 0
  σ := SeedTapeRegister
  initialState := none
  m := seedTapeMachineProgram

private def tapeMachineConfig (label : Option (Fin 4))
    (input markers work : List SeedTapeSymbol) : steinerSeedTapeMachine.Cfg where
  l := label
  var := none
  stk := ![input,markers,work]

theorem tapeStack_update_input (input markers work next : List SeedTapeSymbol) :
    Function.update (![input,markers,work] : Fin 3 → List SeedTapeSymbol) 0 next = ![next,markers,work] := by
  funext i
  fin_cases i <;> simp [Function.update]

theorem tapeStack_update_markers (input markers work next : List SeedTapeSymbol) :
    Function.update (![input,markers,work] : Fin 3 → List SeedTapeSymbol) 1 next = ![input,next,work] := by
  funext i
  fin_cases i <;> simp [Function.update]

theorem tapeStack_update_work (input markers work next : List SeedTapeSymbol) :
    Function.update (![input,markers,work] : Fin 3 → List SeedTapeSymbol) 2 next = ![input,markers,next] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem seedTapeMachine_load_marker (input markers work : List SeedTapeSymbol) :
    steinerSeedTapeMachine.step (tapeMachineConfig (some 0) (none::input) markers work) =
      some (tapeMachineConfig (some 0) input (none::markers) work) := by
  simp [FinTM2.step,steinerSeedTapeMachine,tapeMachineConfig,Turing.TM2.step,Turing.TM2.stepAux,seedTapeMachineProgram,
    tapeStack_update_input,tapeStack_update_markers]
  rfl

private theorem seedTapeMachine_finish_load (bits : List Bool) (markers work : List SeedTapeSymbol) :
    steinerSeedTapeMachine.step (tapeMachineConfig (some 0) (bits.map some) markers work) =
      some (tapeMachineConfig (some 1) (bits.map some) markers work) := by
  cases bits <;>
    simp [FinTM2.step,steinerSeedTapeMachine,tapeMachineConfig,Turing.TM2.step,Turing.TM2.stepAux,seedTapeMachineProgram] <;> rfl

private theorem seedTapeMachine_consume_bit (bit : Bool) (input markers work : List SeedTapeSymbol) :
    steinerSeedTapeMachine.step (tapeMachineConfig (some 1) (some bit::input) (none::markers) work) =
      some (tapeMachineConfig (some 1) input markers (some bit::work)) := by
  simp [FinTM2.step,steinerSeedTapeMachine,tapeMachineConfig,Turing.TM2.step,Turing.TM2.stepAux,seedTapeMachineProgram,
    tapeStack_update_input,tapeStack_update_markers,tapeStack_update_work]
  rfl

private theorem seedTapeMachine_finish_consume (input work : List SeedTapeSymbol) :
    steinerSeedTapeMachine.step (tapeMachineConfig (some 1) input [] work) =
      some (tapeMachineConfig (some 2) (none::input) [] work) := by
  simp [FinTM2.step,steinerSeedTapeMachine,tapeMachineConfig,Turing.TM2.step,Turing.TM2.stepAux,seedTapeMachineProgram,
    tapeStack_update_input]
  rfl

private theorem seedTapeMachine_restore_symbol (symbol : SeedTapeSymbol) (input work : List SeedTapeSymbol) :
    steinerSeedTapeMachine.step (tapeMachineConfig (some 2) input [] (symbol::work)) =
      some (tapeMachineConfig (some 2) (symbol::input) [] work) := by
  simp [FinTM2.step,steinerSeedTapeMachine,tapeMachineConfig,Turing.TM2.step,Turing.TM2.stepAux,seedTapeMachineProgram,
    tapeStack_update_input,tapeStack_update_work]
  rfl

private theorem seedTapeMachine_finish (input : List SeedTapeSymbol) :
    steinerSeedTapeMachine.step (tapeMachineConfig (some 2) input [] []) =
      some (tapeMachineConfig none input [] []) := by
  simp [FinTM2.step,steinerSeedTapeMachine,tapeMachineConfig,Turing.TM2.step,Turing.TM2.stepAux,seedTapeMachineProgram]
  rfl

private def tapeMachineSingleStep {a b : steinerSeedTapeMachine.Cfg}
    (step : steinerSeedTapeMachine.step a = some b) :
    EvalsToInTime steinerSeedTapeMachine.step a (some b) 1 where
  steps := 1
  evals_in_steps := by
    change steinerSeedTapeMachine.step a = some b
    exact step
  steps_le_m := le_rfl

private def seedTapeMachine_load_run (bits : List Bool) (n : ℕ) (markers work : List SeedTapeSymbol) :
    EvalsToInTime steinerSeedTapeMachine.step
      (tapeMachineConfig (some 0) (List.replicate n none ++ bits.map some) markers work)
      (some (tapeMachineConfig (some 1) (bits.map some) (List.replicate n none ++ markers) work))
      (n+1) := by
  induction n generalizing markers with
  | zero =>
    simpa using tapeMachineSingleStep (seedTapeMachine_finish_load bits markers work)
  | succ n ih =>
    have first := tapeMachineSingleStep (seedTapeMachine_load_marker
      (List.replicate n none ++ bits.map some) markers work)
    have rest := ih (none::markers)
    have both := EvalsToInTime.trans _ _ _ _ _ _ first rest
    have marks : List.replicate n none ++ none::markers = List.replicate (n+1) none ++ markers := by
      rw [List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [marks] at both
    simpa only [List.replicate_succ,List.cons_append,Nat.succ_eq_add_one] using both

private def seedTapeMachine_consume_bits (seed tail : List Bool)
    (left work : List SeedTapeSymbol) :
    EvalsToInTime steinerSeedTapeMachine.step
      (tapeMachineConfig (some 1) ((seed ++ tail).map some)
        (List.replicate seed.length none ++ left) work)
      (some (tapeMachineConfig (some 1) (tail.map some) left (seed.reverse.map some ++ work)))
      seed.length := by
  induction seed generalizing work with
  | nil =>
    simpa using EvalsToInTime.refl steinerSeedTapeMachine.step
      (tapeMachineConfig (some 1) (tail.map some) left work)
  | cons bit seed ih =>
    have first := tapeMachineSingleStep (seedTapeMachine_consume_bit bit ((seed ++ tail).map some)
      (List.replicate seed.length none ++ left) work)
    have rest := ih (some bit::work)
    have both := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [List.length_cons,List.replicate_succ,List.cons_append,List.map_cons,
      List.reverse_cons,List.map_append,List.map_nil,List.nil_append,List.singleton_append,List.append_assoc] using both

private def seedTapeMachine_consume_run (seed tail : List Bool) (work : List SeedTapeSymbol) :
    EvalsToInTime steinerSeedTapeMachine.step
      (tapeMachineConfig (some 1) ((seed ++ tail).map some)
        (List.replicate seed.length none) work)
      (some (tapeMachineConfig (some 2) (none::tail.map some) [] (seed.reverse.map some ++ work)))
      (seed.length+1) := by
  have bits := seedTapeMachine_consume_bits seed tail [] work
  have finish := tapeMachineSingleStep (seedTapeMachine_finish_consume (tail.map some) (seed.reverse.map some ++ work))
  simpa only [List.append_nil,Nat.add_comm] using (EvalsToInTime.trans _ _ _ _ _ _ bits finish)

private def seedTapeMachine_restore_run (symbols input : List SeedTapeSymbol) :
    EvalsToInTime steinerSeedTapeMachine.step (tapeMachineConfig (some 2) input [] symbols)
      (some (tapeMachineConfig none (symbols.reverse ++ input) [] [])) (symbols.length+1) := by
  induction symbols generalizing input with
  | nil =>
    simpa using tapeMachineSingleStep (seedTapeMachine_finish input)
  | cons symbol tail ih =>
    have first := tapeMachineSingleStep (seedTapeMachine_restore_symbol symbol input tail)
    have rest := ih (symbol::input)
    have both := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using both

private theorem seedTapeMachine_init (input : List SeedTapeSymbol) :
    initList steinerSeedTapeMachine input = tapeMachineConfig (some 0) input [] [] := by
  unfold initList tapeMachineConfig
  apply congrArg (fun stk : Fin 3 → List SeedTapeSymbol =>
    (⟨some (0:Fin 4),none,stk⟩ : steinerSeedTapeMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem seedTapeMachine_halt (output : List SeedTapeSymbol) :
    haltList steinerSeedTapeMachine output = tapeMachineConfig none output [] [] := by
  unfold haltList tapeMachineConfig
  apply congrArg (fun stk : Fin 3 → List SeedTapeSymbol =>
    (⟨none,none,stk⟩ : steinerSeedTapeMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- The accepted seed split executes in three passes over the prefix,
with one transition per marker, draw, and restored bit, plus three
phase changes. The suffix remains on the input/output stack. -/
def steinerSeedTapeMachine_prefix (seed tail : List Bool) :
    TM2OutputsInTime steinerSeedTapeMachine
      (List.replicate seed.length none ++ (seed++tail).map some)
      (some (seed.map some ++ none::tail.map some)) (3*seed.length+3) := by
  have initial := seedTapeMachine_load_run (seed++tail) seed.length [] []
  have first : EvalsToInTime steinerSeedTapeMachine.step
      (tapeMachineConfig (some 0) (List.replicate seed.length none ++ (seed++tail).map some) [] [])
      (some (tapeMachineConfig (some 1) ((seed++tail).map some) (List.replicate seed.length none) []))
      (seed.length+1) := by simpa only [List.append_nil] using initial
  have second := seedTapeMachine_consume_run seed tail []
  have third := seedTapeMachine_restore_run (seed.reverse.map some) (none::tail.map some)
  rw [List.length_map,List.length_reverse,← List.map_reverse,List.reverse_reverse] at third
  rw [List.append_nil] at second
  have two := EvalsToInTime.trans _ _ _ _ _ _ first second
  have all := EvalsToInTime.trans _ _ _ _ _ _ two third
  unfold TM2OutputsInTime
  change EvalsToInTime steinerSeedTapeMachine.step _ (some (haltList steinerSeedTapeMachine _)) _
  rw [seedTapeMachine_init,seedTapeMachine_halt]
  convert all using 1
  omega

/-- Encode a possibly exhausted request as unary count markers and bits. -/
def encodeSteinerSeedTapeRequest (request : ℕ × List Bool) : List (Option Bool) :=
  List.replicate request.1 none ++ request.2.map some

/-- The split is requested with a count and a tape containing that many bits. -/
structure SteinerSeedTapeInput where
  count : ℕ
  tape : List Bool
  enough : count ≤ tape.length

/-- The tape representation uses unary count markers before the input bits. -/
def encodeSteinerSeedTapeInput (input : SteinerSeedTapeInput) : List (Option Bool) :=
  encodeSteinerSeedTapeRequest (input.count,input.tape)

/-- The resulting prefix and suffix are separated by a single marker. -/
def splitSteinerSeedTape (input : SteinerSeedTapeInput) : List (Option Bool) :=
  (input.tape.take input.count).map some ++ none::(input.tape.drop input.count).map some

def steinerSeedTapeMachine_run (input : SteinerSeedTapeInput) :
    TM2OutputsInTime steinerSeedTapeMachine (encodeSteinerSeedTapeInput input)
      (some (splitSteinerSeedTape input)) (3*input.count+3) := by
  let seed := input.tape.take input.count
  let tail := input.tape.drop input.count
  have seedSize : seed.length = input.count := by
    simp [seed,Nat.min_eq_left input.enough]
  have joined : seed ++ tail = input.tape := List.take_append_drop _ _
  have result := steinerSeedTapeMachine_prefix seed tail
  rw [seedSize,joined] at result
  exact result

/-- The accepted prefix split is polynomial-time in Mathlib's
finite-stack machine model with the supplied unary count encoding. -/
noncomputable def steinerSeedTapeMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerSeedTapeInput id splitSteinerSeedTape where
  tm := steinerSeedTapeMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 3 * Polynomial.X + Polynomial.C 3
  outputsFun input := by
    have result := steinerSeedTapeMachine_run input
    have enlarge : 3*input.count+3 ≤
        (Polynomial.C 3 * Polynomial.X + Polynomial.C 3).eval (encodeSteinerSeedTapeInput input).length := by
      simp [encodeSteinerSeedTapeInput,encodeSteinerSeedTapeRequest]
    change TM2OutputsInTime steinerSeedTapeMachine
      ((encodeSteinerSeedTapeInput input).map id) (some ((splitSteinerSeedTape input).map id)) _
    simpa only [List.map_id_fun,id_eq] using
      (show TM2OutputsInTime steinerSeedTapeMachine (encodeSteinerSeedTapeInput input)
        (some (splitSteinerSeedTape input)) _ from ⟨result.toEvalsTo,result.steps_le_m.trans enlarge⟩)

def encodeSavedSteinerSeed {size : ℕ} (saved : (Vector Bool size × ℕ) × List Bool) :
    List (Option Bool) :=
  saved.1.1.toList.map some ++ none::saved.2.map some

/-- Compare the machine output with the accepted sequential-tape sampler
on exactly the same seed and remaining tape. The number of transitions
depends only on the required seed length. -/
def steinerSeedTapeMachine_refinesSampler {size : ℕ} (count : {b : ℕ // b = size})
    (bits : Fin size → Bool) (tail : List Bool) :
    TM2OutputsInTime steinerSeedTapeMachine
      (List.replicate size none ++ (List.ofFn bits ++ tail).map some)
      (((readSteinerSeedWithWork count steinerBitTapeSource).run (List.ofFn bits ++ tail)).map encodeSavedSteinerSeed)
      (3*size+3) := by
  rw [readSteinerSeedWithWork_tape_prefix]
  simpa only [List.length_ofFn,Option.map_some,encodeSavedSteinerSeed,Vector.toList_ofFn] using
    steinerSeedTapeMachine_prefix (List.ofFn bits) tail

/-- At the algorithm's chosen bit budget, the prefix split satisfies the
same fixed-height polynomial allowance up to the machine's linear factor. -/
theorem steinerSeedTapeMachine_budget_steps {V : Type*} [LinearOrder V] [Fintype V]
    (G : Arcs V) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool) (tail : List Bool) :
    (steinerSeedTapeMachine_refinesSampler ⟨_,rfl⟩ bits tail).steps ≤
      3*(completeSteinerSeedPolynomial (Fintype.card V) G.card height*G.card)+3 := by
  exact (steinerSeedTapeMachine_refinesSampler ⟨_,rfl⟩ bits tail).steps_le_m.trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (steinerBitBudget_polynomial G height)) _)

private theorem seedTapeMachine_enter_rejection (markers work : List SeedTapeSymbol) :
    steinerSeedTapeMachine.step (tapeMachineConfig (some 1) [] (none::markers) work) =
      some (tapeMachineConfig (some 3) [] markers work) := by
  simp [FinTM2.step,steinerSeedTapeMachine,tapeMachineConfig,Turing.TM2.step,Turing.TM2.stepAux,
    seedTapeMachineProgram,tapeStack_update_input,tapeStack_update_markers]
  rfl

private theorem seedTapeMachine_clear_marker (symbol : SeedTapeSymbol) (markers work : List SeedTapeSymbol) :
    steinerSeedTapeMachine.step (tapeMachineConfig (some 3) [] (symbol::markers) work) =
      some (tapeMachineConfig (some 3) [] markers work) := by
  simp [FinTM2.step,steinerSeedTapeMachine,tapeMachineConfig,Turing.TM2.step,Turing.TM2.stepAux,
    seedTapeMachineProgram,tapeStack_update_markers]
  rfl

private theorem seedTapeMachine_clear_work (symbol : SeedTapeSymbol) (work : List SeedTapeSymbol) :
    steinerSeedTapeMachine.step (tapeMachineConfig (some 3) [] [] (symbol::work)) =
      some (tapeMachineConfig (some 3) [] [] work) := by
  simp [FinTM2.step,steinerSeedTapeMachine,tapeMachineConfig,Turing.TM2.step,Turing.TM2.stepAux,
    seedTapeMachineProgram,tapeStack_update_work]
  rfl

private theorem seedTapeMachine_rejected :
    steinerSeedTapeMachine.step (tapeMachineConfig (some 3) [] [] []) =
      some (tapeMachineConfig none [] [] []) := by
  simp [FinTM2.step,steinerSeedTapeMachine,tapeMachineConfig,Turing.TM2.step,Turing.TM2.stepAux,
    seedTapeMachineProgram]
  rfl

private def seedTapeMachine_clear_work_run (work : List SeedTapeSymbol) :
    EvalsToInTime steinerSeedTapeMachine.step (tapeMachineConfig (some 3) [] [] work)
      (some (tapeMachineConfig none [] [] [])) (work.length+1) := by
  induction work with
  | nil => exact tapeMachineSingleStep seedTapeMachine_rejected
  | cons bit work ih =>
    exact EvalsToInTime.trans _ _ _ _ _ _ (tapeMachineSingleStep (seedTapeMachine_clear_work bit work)) ih

private def seedTapeMachine_clear_rejection (markers work : List SeedTapeSymbol) :
    EvalsToInTime steinerSeedTapeMachine.step (tapeMachineConfig (some 3) [] markers work)
      (some (tapeMachineConfig none [] [] [])) (work.length+markers.length+1) := by
  induction markers with
  | nil => exact seedTapeMachine_clear_work_run work
  | cons marker markers ih =>
    have first := tapeMachineSingleStep (seedTapeMachine_clear_marker marker markers work)
    have both := EvalsToInTime.trans _ _ _ _ _ _ first ih
    simpa only [List.length_cons,Nat.add_assoc] using both

/-- On an exhausted tape, return the empty output after clearing both
auxiliary stacks. Successful output always contains the separator. -/
def steinerSeedTapeMachine_short (count : ℕ) (tape : List Bool) (short : tape.length < count) :
    TM2OutputsInTime steinerSeedTapeMachine (List.replicate count none ++ tape.map some) (some []) (3*count+3) := by
  let left := count-tape.length-1
  have markerCount : tape.length+(left+1) = count := by dsimp [left]; omega
  have markers : List.replicate count (none : SeedTapeSymbol) =
      List.replicate tape.length none ++ none::List.replicate left none := by
    rw [← markerCount,List.replicate_add,List.replicate_succ]
  have loaded := seedTapeMachine_load_run tape count [] []
  rw [List.append_nil,markers] at loaded
  have consumed := seedTapeMachine_consume_bits tape [] (none::List.replicate left none) []
  simp only [List.append_nil,List.map_nil] at consumed
  have entering := tapeMachineSingleStep (seedTapeMachine_enter_rejection
    (List.replicate left none) (tape.reverse.map some))
  have final : EvalsToInTime steinerSeedTapeMachine.step
      (tapeMachineConfig (some 3) [] (List.replicate left none) (tape.reverse.map some))
      (some (tapeMachineConfig none [] [] [])) (tape.length+left+1) := by
    simpa only [List.length_map,List.length_reverse,List.length_replicate] using
      seedTapeMachine_clear_rejection (List.replicate left none) (tape.reverse.map some)
  have covered := EvalsToInTime.trans _ _ _ _ _ _ loaded consumed
  have cleaning := EvalsToInTime.trans _ _ _ _ _ _ covered entering
  have rejected := EvalsToInTime.trans _ _ _ _ _ _ cleaning final
  have bound := rejected.steps_le_m
  have upper : rejected.steps ≤ 3*count+3 := by omega
  unfold TM2OutputsInTime
  change EvalsToInTime steinerSeedTapeMachine.step _ (some (haltList steinerSeedTapeMachine [])) _
  rw [seedTapeMachine_init,seedTapeMachine_halt,markers]
  exact ⟨rejected.toEvalsTo,upper⟩

/-- A failed sequential-tape run is represented by the empty output,
while the successful representation contains its separator. -/
def steinerSeedTapeMachine_refinesExhaustion {size : ℕ} (count : {b : ℕ // b = size})
    (tape : List Bool) (short : tape.length < size) :
    TM2OutputsInTime steinerSeedTapeMachine (List.replicate size none ++ tape.map some)
      (some ((((readSteinerSeedWithWork count steinerBitTapeSource).run tape).map encodeSavedSteinerSeed).getD []))
      (3*size+3) := by
  rw [readSteinerSeedWithWork_tape_none count tape short]
  exact steinerSeedTapeMachine_short size tape short

/-- An empty output reports exhaustion. An accepted output separates
the seed from the suffix, including if either list is empty. -/
def splitSteinerSeedTapeOrReject (request : ℕ × List Bool) : List (Option Bool) :=
  if enough : request.1 ≤ request.2.length then splitSteinerSeedTape ⟨request.1,request.2,enough⟩ else []

theorem splitSteinerSeedTapeOrReject_eq_nil_iff (request : ℕ × List Bool) :
    splitSteinerSeedTapeOrReject request = [] ↔ request.2.length < request.1 := by
  by_cases enough : request.1 ≤ request.2.length
  · simp [splitSteinerSeedTapeOrReject,splitSteinerSeedTape,enough,not_lt_of_ge enough]
  · simp [splitSteinerSeedTapeOrReject,enough,lt_of_not_ge enough]

/-- The machine produces the accepted or exhausted result for every
count and finite bit list. -/
def steinerSeedTapeMachine_runOrReject (request : ℕ × List Bool) :
    TM2OutputsInTime steinerSeedTapeMachine (encodeSteinerSeedTapeRequest request)
      (some (splitSteinerSeedTapeOrReject request)) (3*request.1+3) := by
  by_cases enough : request.1 ≤ request.2.length
  · rw [splitSteinerSeedTapeOrReject,dite_eq_left enough]
    exact steinerSeedTapeMachine_run ⟨request.1,request.2,enough⟩
  · rw [splitSteinerSeedTapeOrReject,dite_eq_right enough]
    exact steinerSeedTapeMachine_short request.1 request.2 (lt_of_not_ge enough)

/-- Total seed splitting is polynomial-time on the specified encoding,
including when the supplied tape is too short. -/
noncomputable def steinerSeedTapeMachine_totalPolytime :
    TM2ComputableInPolyTime encodeSteinerSeedTapeRequest id splitSteinerSeedTapeOrReject where
  tm := steinerSeedTapeMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 3 * Polynomial.X + Polynomial.C 3
  outputsFun request := by
    have result := steinerSeedTapeMachine_runOrReject request
    have enlarge : 3*request.1+3 ≤
        (Polynomial.C 3 * Polynomial.X + Polynomial.C 3).eval (encodeSteinerSeedTapeRequest request).length := by
      simp [encodeSteinerSeedTapeRequest]
    change TM2OutputsInTime steinerSeedTapeMachine ((encodeSteinerSeedTapeRequest request).map id)
      (some ((splitSteinerSeedTapeOrReject request).map id)) _
    simpa only [List.map_id_fun,id_eq] using
      (show TM2OutputsInTime steinerSeedTapeMachine (encodeSteinerSeedTapeRequest request)
        (some (splitSteinerSeedTapeOrReject request)) _ from ⟨result.toEvalsTo,result.steps_le_m.trans enlarge⟩)

/-- The same finite machine refines the sequential sampler on every
tape, using an empty output to represent its exhaustion. -/
def steinerSeedTapeMachine_refinesFiniteSampler {size : ℕ} (count : {b : ℕ // b = size})
    (tape : List Bool) :
    TM2OutputsInTime steinerSeedTapeMachine (encodeSteinerSeedTapeRequest (size,tape))
      (some ((((readSteinerSeedWithWork count steinerBitTapeSource).run tape).map encodeSavedSteinerSeed).getD []))
      (3*size+3) := by
  by_cases enough : size ≤ tape.length
  · let seed := tape.take size
    let tail := tape.drop size
    have sizeEq : seed.length = size := by simp [seed,Nat.min_eq_left enough]
    let bits : Fin size → Bool := fun i => seed.get (Fin.cast sizeEq.symm i)
    have asList : List.ofFn bits = seed := by
      apply List.ext_getElem
      · simp [sizeEq]
      · intro j left right
        simp [bits,List.get_eq_getElem]
    have joined : List.ofFn bits ++ tail = tape := by
      rw [asList]
      exact List.take_append_drop _ _
    have success := readSteinerSeedWithWork_tape_prefix count bits tail
    have certificate := steinerSeedTapeMachine_refinesSampler count bits tail
    rw [joined] at success certificate
    simpa only [encodeSteinerSeedTapeRequest,success,Option.map_some,Option.getD_some] using certificate
  · exact steinerSeedTapeMachine_refinesExhaustion count tape (lt_of_not_ge enough)

/-- The fixed-height graph bound applies to every finite seed tape,
including exhausted tapes. -/
theorem steinerSeedTapeMachine_finite_budget_steps {V : Type*} [LinearOrder V] [Fintype V]
    (G : Arcs V) (height : ℕ) (tape : List Bool) :
    (steinerSeedTapeMachine_refinesFiniteSampler (size := steinerBitBudget G height) ⟨_,rfl⟩ tape).steps ≤
      3*(completeSteinerSeedPolynomial (Fintype.card V) G.card height*G.card)+3 := by
  exact (steinerSeedTapeMachine_refinesFiniteSampler (size := steinerBitBudget G height) ⟨_,rfl⟩ tape).steps_le_m.trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (steinerBitBudget_polynomial G height)) _)

end OnlineReachabilityPreservers
