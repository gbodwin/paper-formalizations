import LightEFTSpanners.StoredWeightLookup
open LightEFTSpanners.StoredWeightLookup
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredWeightLookup.steps
  let some c := env.find? name | throwError "steps missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "steps not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: steps safe, total, computable, explicit List.rec, no partial companion"
example (i j : ℕ) : steps i j [] = 1 := rfl
example (j : ℕ) (row : List ℚ) (rows : LightEFTSpanners.StoredRecords.Weights) :
    steps 0 j (row::rows) = rowSteps j row+1 := rfl
example (i j : ℕ) (row : List ℚ) (rows : LightEFTSpanners.StoredRecords.Weights) :
    steps (i+1) j (row::rows) = steps i j rows+1 := rfl
#eval do
  let checks := [
    decide (steps 0 0 [] = 1),
    decide (steps 100000000000000000000 100000000000000000000 [] = 1),
    decide (steps 0 0 [[]] = 2),
    decide (steps 0 100000000000000000000 [[],[9]] = 2),
    decide (steps 1 0 [[],[9]] = 3),
    decide (steps 2 0 [[],[9]] = 3),
    decide (steps 100000000000000000000 0 [[],[9]] = 3),
    decide (steps 0 0 [[-3/2,0,5/7],[],[-9]] = 2),
    decide (steps 0 1 [[-3/2,0,5/7],[],[-9]] = 3),
    decide (steps 0 2 [[-3/2,0,5/7],[],[-9]] = 4),
    decide (steps 0 3 [[-3/2,0,5/7],[],[-9]] = 5),
    decide (steps 0 100000000000000000000 [[-3/2,0,5/7],[],[-9]] = 5),
    decide (steps 1 0 [[-3/2,0,5/7],[],[-9]] = 3),
    decide (steps 1 99 [[-3/2,0,5/7],[],[-9]] = 3),
    decide (steps 2 0 [[-3/2,0,5/7],[],[-9]] = 4),
    decide (steps 2 1 [[-3/2,0,5/7],[],[-9]] = 5),
    decide (steps 3 99 [[-3/2,0,5/7],[],[-9]] = 4),
    decide (steps 15 15 (List.replicate 16 (List.replicate 16 (-5/13))) = 32),
    decide (steps 15 16 (List.replicate 16 (List.replicate 16 (-5/13))) = 33),
    decide (steps 16 16 (List.replicate 16 (List.replicate 16 (-5/13))) = 17)]
  unless checks.all id do throw (IO.userError "Exact full lookup-count fixtures failed")
  IO.println s!"PASS: {checks.length} complete natural transition-count fixtures; ragged or empty matrices, arbitrary row/column indices, row and cell traversal, misses and final halt"
