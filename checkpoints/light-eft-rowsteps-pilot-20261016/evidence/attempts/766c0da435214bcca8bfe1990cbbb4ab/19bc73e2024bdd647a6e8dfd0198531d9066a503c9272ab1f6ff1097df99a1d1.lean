import LightEFTSpanners.StoredWeightLookup
open LightEFTSpanners.StoredWeightLookup
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredWeightLookup.rowSteps
  let some c := env.find? name | throwError "rowSteps missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "rowSteps not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.rowSteps.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.rowSteps.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: rowSteps safe, total, computable, explicit List.rec, no partial companion"
example (j : ℕ) : rowSteps j [] = 1 := rfl
example (w : ℚ) (ws : List ℚ) : rowSteps 0 (w::ws) = 1 := rfl
example (j : ℕ) (w : ℚ) (ws : List ℚ) : rowSteps (j+1) (w::ws) = rowSteps j ws+1 := rfl
#eval do
  let checks := [
    decide (rowSteps 0 [] = 1),
    decide (rowSteps 1 [] = 1),
    decide (rowSteps 100000000000000000000 [] = 1),
    decide (rowSteps 0 [7] = 1),
    decide (rowSteps 0 [-7] = 1),
    decide (rowSteps 0 [0] = 1),
    decide (rowSteps 1 [7] = 2),
    decide (rowSteps 2 [7] = 2),
    decide (rowSteps 100000000000000000000 [-7] = 2),
    decide (rowSteps 0 [-3/2,0,5/7,-9] = 1),
    decide (rowSteps 1 [-3/2,0,5/7,-9] = 2),
    decide (rowSteps 2 [-3/2,0,5/7,-9] = 3),
    decide (rowSteps 3 [-3/2,0,5/7,-9] = 4),
    decide (rowSteps 4 [-3/2,0,5/7,-9] = 5),
    decide (rowSteps 5 [-3/2,0,5/7,-9] = 5),
    decide (rowSteps 100000000000000000000 [-3/2,0,5/7,-9] = 5),
    decide (rowSteps 1 [0,999999999999999999999/11] = 2),
    decide (rowSteps 2 [3,3,-3] = 3),
    decide (rowSteps 15 (List.replicate 16 (-5/13)) = 16),
    decide (rowSteps 16 (List.replicate 16 (-5/13)) = 17)]
  unless checks.all id do throw (IO.userError "Exact transition-count fixtures failed")
  IO.println s!"PASS: {checks.length} complete natural transition-count fixtures; empty, in-range, last-cell, first-miss, huge index, signed payloads and final halt transition"
