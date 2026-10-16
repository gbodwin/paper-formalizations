import LightEFTSpanners.StoredWeightLookup
open LightEFTSpanners.StoredWeightLookup
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredWeightLookup.value
  let some c := env.find? name | throwError "value missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "value not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: value safe, total, computable, explicit List.rec, no partial companion"
example (i j : ℕ) : value i j [] = 0 := rfl
example (j : ℕ) (row : List ℚ) (rows : LightEFTSpanners.StoredRecords.Weights) :
    value 0 j (row::rows) = rowValue j row := rfl
example (i j : ℕ) (row : List ℚ) (rows : LightEFTSpanners.StoredRecords.Weights) :
    value (i+1) j (row::rows) = value i j rows := rfl
#eval do
  let checks := [
    decide (value 0 0 [] = 0),
    decide (value 100000000000000000000 100000000000000000000 [] = 0),
    decide (value 0 0 [[]] = 0),
    decide (value 0 99999999999999999999 [[],[9]] = 0),
    decide (value 0 0 [[],[9]] = 0),
    decide (value 1 0 [[],[9]] = 9),
    decide (value 2 0 [[],[9]] = 0),
    decide (value 0 0 [[-3/2,0,5/7],[],[-9]] = -3/2),
    decide (value 0 1 [[-3/2,0,5/7],[],[-9]] = 0),
    decide (value 0 2 [[-3/2,0,5/7],[],[-9]] = 5/7),
    decide (value 0 3 [[-3/2,0,5/7],[],[-9]] = 0),
    decide (value 1 0 [[-3/2,0,5/7],[],[-9]] = 0),
    decide (value 2 0 [[-3/2,0,5/7],[],[-9]] = -9),
    decide (value 2 1 [[-3/2,0,5/7],[],[-9]] = 0),
    decide (value 3 0 [[-3/2,0,5/7],[],[-9]] = 0),
    decide (value 100000000000000000000 0 [[1],[2]] = 0),
    decide (value 1 100000000000000000000 [[1],[2]] = 0),
    decide (value 1 1 [[3,3],[3,-3]] = -3),
    decide (value 1 1 [[],[2,-999999999999999999999/11]] = -999999999999999999999/11),
    decide (value 15 2 (List.replicate 16 [0,1,-5/13]) = -5/13)]
  unless checks.all id do throw (IO.userError "Exact ragged matrix lookup fixtures failed")
  IO.println s!"PASS: {checks.length} complete rational output fixtures; ragged matrices, empty selected rows, signed payloads, positional order, arbitrary indices and out-of-range zero"
