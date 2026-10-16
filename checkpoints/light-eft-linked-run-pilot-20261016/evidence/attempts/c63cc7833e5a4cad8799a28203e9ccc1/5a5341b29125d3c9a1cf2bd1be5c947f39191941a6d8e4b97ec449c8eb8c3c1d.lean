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
    decide (run 3 [] 8 9 (-2) 10 (.halt true) = .halt true),
    decide (run 3 [] 8 9 (-2) 5 (.halt false) = .halt false),
    decide (run 0 [] 0 0 0 1 (.init 0 0 []) = .revInit [] []),
    decide (run 2 [] 0 7 0 1 (.init 2 7 [some (-2)]) = .init 1 8 [some 0,some (-2)]),
    decide (run 2 [] 0 0 0 1 (.revInit [none,some 1] [some (-3)]) = .revInit [some 1] [none,some (-3)]),
    decide (run 2 [] 0 0 0 1 (.revInit [] [some 3]) = .round 2 [some 3]),
    decide (run 2 [] 7 0 0 1 (.round 0 [none]) = .lookup 7 [none]),
    decide (run 2 [[some (-1)]] 0 0 0 1 (.round 1 [some 0]) = .row 0 [some 0] [[some (-1)]] [some 0] []),
    decide (run 2 [] 0 0 0 1 (.row 3 [none] [] [some 1] [some 2]) = .revRound 3 [some 2] []),
    decide (run 2 [] 0 0 0 1 (.row 3 [none] [[some 1]] [] [some 2]) = .revRound 3 [some 2] []),
    decide (run 2 [] 0 0 0 1 (.scan 3 [] [] [] [] [some (-1/2)] [some (-2)] (some 0)) =
      .scan 3 [] [] [] [] [] [] (some (-5/2))),
    decide (run 2 [] 0 0 0 1 (.scan 3 [] [] [] [] [none] [] (some (-2))) = .row 3 [] [] [] [some (-2)]),
    decide (run 2 [] 0 0 0 1 (.revRound 3 [] [none]) = .round 3 [none]),
    decide (run 2 [] 0 0 0 1 (.revRound 3 [some 1] [none]) = .revRound 3 [] [some 1,none]),
    decide (run 2 [] 0 0 0 1 (.lookup 0 [none]) = .halt false),
    decide (run 2 [] 0 0 (-1) 1 (.lookup 0 [some (-1)]) = .halt true),
    decide (run 2 [] 0 0 0 1 (.lookup 0 [some 1]) = .halt false),
    decide (run 2 [] 0 0 0 1 (.lookup 7 []) = .halt false),
    decide (run 2 [] 0 0 0 1 (.lookup 2 [some 0,none]) = .lookup 1 [none]),
    decide (run 0 [] 0 0 0 3 (.init 0 0 []) = .lookup 0 []),
    decide (run 0 [] 0 0 0 4 (.init 0 0 []) = .halt false),
    decide (run 0 [] 0 0 0 100 (.init 0 0 []) = .halt false),
    decide (run 1 [[none]] 0 0 0 100 (.init 1 0 []) = .halt true),
    decide (run 1 [[none]] 9 0 0 100 (.init 1 0 []) = .halt false),
    decide (run 1 [[none]] 0 0 (-1) 100 (.init 1 0 []) = .halt false),
    decide (run 1 [[some (-1)]] 0 0 (-1) 100 (.init 1 0 []) = .halt true),
    decide (run 2 [] 0 0 0 100 (.init 2 0 []) = .halt false)]
  unless checks.all id do throw (IO.userError "Full-state controller fixtures failed")
  IO.println s!"PASS: {checks.length} full-state fixtures: terminal, every state constructor, exhausted fuel, empty/ragged inputs, out-of-range lookup, negative/fractional cells and complete runs"
