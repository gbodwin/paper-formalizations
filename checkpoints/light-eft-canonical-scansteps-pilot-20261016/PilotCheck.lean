import LightEFTSpanners.StoredCanonicalHosts
open LightEFTSpanners.StoredCanonicalHosts
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredCanonicalHosts.scanSteps
  let some c := env.find? name | throwError "scanSteps missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "scanSteps not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: scanSteps safe, total, computable, explicit List.rec, no partial companion"
example (es : List LightEFTSpanners.StoredEdges.Edge) : scanSteps es [] = 1 := rfl
example (es : List LightEFTSpanners.StoredEdges.Edge) (r : Component) (rs : List Component) :
    scanSteps es (r::rs) = LightEFTSpanners.StoredComponentHostFilter.steps r.2 es+2+scanSteps es rs := rfl
#eval do
  let checks := [
    decide (scanSteps [] [] = 1),
    decide (scanSteps [(0,1),(1,1)] [] = 1),
    decide (scanSteps [] [(0,[])] = 5),
    decide (scanSteps [] [(999,[99,99])] = 5),
    decide (scanSteps [] [(0,[]),(5,[1]),(99,[9,9])] = 13),
    decide (scanSteps [(0,0)] [(0,[])] = 6),
    decide (scanSteps [(0,1)] [(0,[])] = 8),
    decide (scanSteps [(0,1)] [(0,[0])] = 11),
    decide (scanSteps [(0,1)] [(0,[1])] = 9),
    decide (scanSteps [(0,1)] [(0,[0,1])] = 12),
    decide (scanSteps [(0,1)] [(0,[1,0])] = 12),
    decide (scanSteps [(0,1)] [(0,[0,0,1])] = 13),
    decide (scanSteps [(0,1)] [(0,[9,0,1])] = 14),
    decide (scanSteps [(0,1),(1,0)] [(0,[0,1])] = 19),
    decide (scanSteps [(0,1),(0,1),(0,0)] [(0,[0,1])] = 20),
    decide (scanSteps [(0,1)] [(999,[]),(999,[0]),(999,[0,1])] = 29),
    decide (scanSteps [(100000000000000000000,1)] [(99999999999999999999,[100000000000000000000,1])] = 12),
    decide (scanSteps (List.replicate 16 (0,0)) [(0,[])] = 21),
    decide (scanSteps (List.replicate 16 (0,1)) [(0,[])] = 53),
    decide (scanSteps [] (List.replicate 16 (999,[])) = 65)]
  unless checks.all id do throw (IO.userError "Exact canonical host scan-count fixtures failed")
  IO.println s!"PASS: {checks.length} complete natural scan-count fixtures; empty input, filter plus two plus tail, loops, missing endpoints, duplicate vertices/edges, arbitrary labels/components, huge naturals and repeated records"
