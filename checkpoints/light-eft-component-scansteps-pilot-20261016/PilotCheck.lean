import LightEFTSpanners.StoredComponentHostTrace
open LightEFTSpanners.StoredComponentHostFilter
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredComponentHostFilter.scanSteps
  let some c := env.find? name | throwError "scanSteps missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "scanSteps not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: scanSteps safe, total, computable, explicit List.rec, no partial companion"
example (vs : List ℕ) : scanSteps vs [] = 1 := rfl
example (vs : List ℕ) (e : LightEFTSpanners.StoredEdges.Edge) (es : List LightEFTSpanners.StoredEdges.Edge) :
    scanSteps vs (e::es) = edgeSteps vs e+scanSteps vs es := rfl
example (vs : List ℕ) (es : List LightEFTSpanners.StoredEdges.Edge) :
    steps vs es = scanSteps vs es+(value vs es).length+1 := rfl
#eval do
  let checks := [
    decide (scanSteps [] [] = 1),
    decide (scanSteps [9,9,0] [] = 1),
    decide (scanSteps [] [(0,0)] = 2),
    decide (scanSteps [0,0] [(0,0)] = 2),
    decide (scanSteps [] [(0,1)] = 4),
    decide (scanSteps [0] [(0,1)] = 7),
    decide (scanSteps [1] [(0,1)] = 5),
    decide (scanSteps [9] [(0,1)] = 5),
    decide (scanSteps [0,1] [(0,1)] = 7),
    decide (scanSteps [1,0] [(0,1)] = 7),
    decide (scanSteps [0,0,1] [(0,1)] = 8),
    decide (scanSteps [9,0,1] [(0,1)] = 9),
    decide (scanSteps [0,1] [(0,1),(1,0)] = 13),
    decide (scanSteps [0,1] [(0,1),(0,1),(0,0)] = 14),
    decide (scanSteps [] [(0,0),(0,1),(1,0)] = 8),
    decide (scanSteps [100000000000000000000,1] [(100000000000000000000,1)] = 7),
    decide (scanSteps [] (List.replicate 16 (0,0)) = 17),
    decide (scanSteps [] (List.replicate 16 (0,1)) = 49),
    decide (scanSteps [0,1] (List.replicate 16 (0,1)) = 97),
    decide (scanSteps (List.replicate 16 9) [(0,1)] = 20)]
  unless checks.all id do throw (IO.userError "Exact component filter scan-count fixtures failed")
  IO.println s!"PASS: {checks.length} complete natural scan-count fixtures; empty input, loops, missing endpoints, duplicate vertices/edges, huge naturals and long lists; reversal separately charged"
