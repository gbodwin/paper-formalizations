import Mathlib.Computability.TuringMachine.Computable
import OnlineReachabilityPreservers.SteinerBinarySeedTape

/-! A finite stack machine for the accepted Steiner seed prefix. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev SeedTapeSymbol := Option Bool
private abbrev SeedTapeRegister := Option SeedTapeSymbol
private abbrev SeedTapeStmt := Turing.TM2.Stmt (fun _ : Fin 3 => SeedTapeSymbol) (Fin 3) SeedTapeRegister

private def seedTapeMachineProgram (label : Fin 3) : SeedTapeStmt :=
  if label = 0 then
    peek 0 (fun _ symbol => symbol) <|
      branch (· == some none)
        (pop 0 (fun _ _ => none) <| push 1 (fun _ => none) <| goto (fun _ => 0))
        (load (fun _ => none) <| goto (fun _ => 1))
  else if label = 1 then
    peek 1 (fun _ symbol => symbol) <|
      branch Option.isSome
        (pop 1 (fun _ _ => none) <| pop 0 (fun _ symbol => symbol) <|
          push 2 (·.getD none) <| load (fun _ => none) <| goto (fun _ => 1))
        (push 0 (fun _ => none) <| load (fun _ => none) <| goto (fun _ => 2))
  else
    peek 2 (fun _ symbol => symbol) <|
      branch Option.isSome
        (pop 2 (fun _ symbol => symbol) <| push 0 (·.getD none) <|
          load (fun _ => none) <| goto (fun _ => 2))
        (load (fun _ => none) halt)

/-- Load one marker per requested bit, transfer that prefix, then restore
it before a separator and the untouched suffix on the output stack. -/
abbrev steinerSeedTapeMachine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 0
  Γ _ := SeedTapeSymbol
  Λ := Fin 3
  main := 0
  σ := SeedTapeRegister
  initialState := none
  m := seedTapeMachineProgram

private def tapeMachineConfig (label : Option (Fin 3))
    (input markers work : List SeedTapeSymbol) : steinerSeedTapeMachine.Cfg where
  l := label
  var := none
  stk := ![input,markers,work]

private theorem tapeStack_update_input (input markers work next : List SeedTapeSymbol) :
    Function.update (![input,markers,work] : Fin 3 → List SeedTapeSymbol) 0 next = ![next,markers,work] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem tapeStack_update_markers (input markers work next : List SeedTapeSymbol) :
    Function.update (![input,markers,work] : Fin 3 → List SeedTapeSymbol) 1 next = ![input,next,work] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem tapeStack_update_work (input markers work next : List SeedTapeSymbol) :
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

private def seedTapeMachine_consume_run (seed tail : List Bool) (work : List SeedTapeSymbol) :
    EvalsToInTime steinerSeedTapeMachine.step
      (tapeMachineConfig (some 1) ((seed ++ tail).map some)
        (List.replicate seed.length none) work)
      (some (tapeMachineConfig (some 2) (none::tail.map some) [] (seed.reverse.map some ++ work)))
      (seed.length+1) := by
  induction seed generalizing work with
  | nil =>
    simpa using tapeMachineSingleStep (seedTapeMachine_finish_consume (tail.map some) work)
  | cons bit seed ih =>
    have first := tapeMachineSingleStep (seedTapeMachine_consume_bit bit ((seed ++ tail).map some)
      (List.replicate seed.length none) work)
    have rest := ih (some bit::work)
    have both := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [List.length_cons,List.replicate_succ,List.cons_append,List.map_cons,
      List.reverse_cons,List.map_append,List.map_nil,List.nil_append,List.singleton_append,List.append_assoc] using both

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
    (⟨some (0:Fin 3),none,stk⟩ : steinerSeedTapeMachine.Cfg))
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

/-- The split is requested with a count and a tape containing that many bits. -/
structure SteinerSeedTapeInput where
  count : ℕ
  tape : List Bool
  enough : count ≤ tape.length

/-- The tape representation uses unary count markers before the input bits. -/
def encodeSteinerSeedTapeInput (input : SteinerSeedTapeInput) : List (Option Bool) :=
  List.replicate input.count none ++ input.tape.map some

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
      simp [encodeSteinerSeedTapeInput]
    change TM2OutputsInTime steinerSeedTapeMachine
      ((encodeSteinerSeedTapeInput input).map id) (some ((splitSteinerSeedTape input).map id)) _
    simpa only [List.map_id_fun,id_eq] using
      (show TM2OutputsInTime steinerSeedTapeMachine (encodeSteinerSeedTapeInput input)
        (some (splitSteinerSeedTape input)) _ from ⟨result.toEvalsTo,result.steps_le_m.trans enlarge⟩)

private def encodeSavedSteinerSeed {size : ℕ} (saved : (Vector Bool size × ℕ) × List Bool) :
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

end OnlineReachabilityPreservers
