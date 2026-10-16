import LightEFTSpanners.LinkedDistanceMachine
open LightEFTSpanners.LinkedDistance
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.LinkedDistance.run
  let some c := env.find? name | throwError "run missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "run not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `Nat.rec do throwError "Nat.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: run safe, total, computable, explicit Nat.rec, no partial companion"
example (size : ℕ) (M : Matrix) (source target : ℕ) (budget : ℚ) (s : State) :
    run size M source target budget 0 s = s := rfl
example (size : ℕ) (M : Matrix) (source target : ℕ) (budget : ℚ) (k : ℕ) (s : State) :
    run size M source target budget (k+1) s =
      match transition size M source target budget s with
      | none => s
      | some t => run size M source target budget k t := rfl
#eval do
  let checks := [
    decide (run 3 [] 8 9 (-2) 10 (State.halt true) = State.halt true),
    decide (run 3 [] 8 9 (-2) 5 (State.halt false) = State.halt false),
    decide (run 0 [] 0 0 0 1 (State.init 0 0 []) = State.revInit [] []),
    decide (run 2 [] 0 7 0 1 (State.init 2 7 [some (-2)]) = State.init 1 8 [some 0,some (-2)]),
    decide (run 2 [] 0 0 0 1 (State.revInit [none,some 1] [some (-3)]) = State.revInit [some 1] [none,some (-3)]),
    decide (run 2 [] 0 0 0 1 (State.revInit [] [some 3]) = State.round 2 [some 3]),
    decide (run 2 [] 7 0 0 1 (State.round 0 [none]) = State.lookup 7 [none]),
    decide (run 2 [[some (-1)]] 0 0 0 1 (State.round 1 [some 0]) = State.row 0 [some 0] [[some (-1)]] [some 0] []),
    decide (run 2 [] 0 0 0 1 (State.row 3 [none] [] [some 1] [some 2]) = State.revRound 3 [some 2] []),
    decide (run 2 [] 0 0 0 1 (State.row 3 [none] [[some 1]] [] [some 2]) = State.revRound 3 [some 2] []),
    decide (run 2 [] 0 0 0 1 (State.scan 3 [] [] [] [] [some (-1/2)] [some (-2)] (some 0)) =
      State.scan 3 [] [] [] [] [] [] (some (-5/2))),
    decide (run 2 [] 0 0 0 1 (State.scan 3 [] [] [] [] [none] [] (some (-2))) = State.row 3 [] [] [] [some (-2)]),
    decide (run 2 [] 0 0 0 1 (State.revRound 3 [] [none]) = State.round 3 [none]),
    decide (run 2 [] 0 0 0 1 (State.revRound 3 [some 1] [none]) = State.revRound 3 [] [some 1,none]),
    decide (run 2 [] 0 0 0 1 (State.lookup 0 [none]) = State.halt false),
    decide (run 2 [] 0 0 (-1) 1 (State.lookup 0 [some (-1)]) = State.halt true),
    decide (run 2 [] 0 0 0 1 (State.lookup 0 [some 1]) = State.halt false),
    decide (run 2 [] 0 0 0 1 (State.lookup 7 []) = State.halt false),
    decide (run 2 [] 0 0 0 1 (State.lookup 2 [some 0,none]) = State.lookup 1 [none]),
    decide (run 0 [] 0 0 0 3 (State.init 0 0 []) = State.lookup 0 []),
    decide (run 0 [] 0 0 0 4 (State.init 0 0 []) = State.halt false),
    decide (run 0 [] 0 0 0 100 (State.init 0 0 []) = State.halt false),
    decide (run 1 [[none]] 0 0 0 100 (State.init 1 0 []) = State.halt true),
    decide (run 1 [[none]] 9 0 0 100 (State.init 1 0 []) = State.halt false),
    decide (run 1 [[none]] 0 0 (-1) 100 (State.init 1 0 []) = State.halt false),
    decide (run 1 [[some (-1)]] 0 0 (-1) 100 (State.init 1 0 []) = State.halt true),
    decide (run 2 [] 0 0 0 100 (State.init 2 0 []) = State.halt false)]
  unless checks.all id do throw (IO.userError "Full-state controller fixtures failed")
  IO.println s!"PASS: {checks.length} full-state fixtures: terminal, every state constructor, exhausted fuel, empty/ragged inputs, out-of-range lookup, negative/fractional cells and complete runs"
