import LightEFTSpanners.StoredWeightLookup
open LightEFTSpanners.StoredWeightLookup
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredWeightLookup.rowValue
  let some c := env.find? name | throwError "rowValue missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "rowValue not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: rowValue safe, total, computable, explicit List.rec, no partial companion"
example (j : ℕ) : rowValue j [] = 0 := rfl
example (w : ℚ) (ws : List ℚ) : rowValue 0 (w::ws) = w := rfl
example (j : ℕ) (w : ℚ) (ws : List ℚ) : rowValue (j+1) (w::ws) = rowValue j ws := rfl
#eval do
  let checks := [
    decide (rowValue 0 [] = 0),
    decide (rowValue 1 [] = 0),
    decide (rowValue 100000000000000000000 [] = 0),
    decide (rowValue 0 [7] = 7),
    decide (rowValue 0 [-7] = -7),
    decide (rowValue 0 [0] = 0),
    decide (rowValue 1 [7] = 0),
    decide (rowValue 100000000000000000000 [-7] = 0),
    decide (rowValue 0 [-3/2,0,5/7,-9] = -3/2),
    decide (rowValue 1 [-3/2,0,5/7,-9] = 0),
    decide (rowValue 2 [-3/2,0,5/7,-9] = 5/7),
    decide (rowValue 3 [-3/2,0,5/7,-9] = -9),
    decide (rowValue 4 [-3/2,0,5/7,-9] = 0),
    decide (rowValue 0 [0,9] = 0),
    decide (rowValue 1 [0,9] = 9),
    decide (rowValue 1 [3,3,-3] = 3),
    decide (rowValue 2 [3,3,-3] = -3),
    decide (rowValue 1 [2,-999999999999999999999/11] = -999999999999999999999/11),
    decide (rowValue 15 (List.replicate 16 (-5/13)) = -5/13),
    decide (rowValue 16 (List.replicate 16 (-5/13)) = 0)]
  unless checks.all id do throw (IO.userError "Exact rational lookup fixtures failed")
  IO.println s!"PASS: {checks.length} complete rational output fixtures; signed, fractional, zero, arbitrary indices, positional order, duplicates, large payloads and out-of-range zero"
