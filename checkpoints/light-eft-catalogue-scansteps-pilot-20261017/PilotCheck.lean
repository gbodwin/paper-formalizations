import LightEFTSpanners.StoredComponentCatalogue
open LightEFTSpanners.StoredComponentCatalogue
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredComponentCatalogue.scanSteps
  let some c := env.find? name | throwError "scanSteps missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "scanSteps not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: scanSteps safe, total, computable, explicit List.rec, no partial companion"
open LightEFTSpanners.StoredComponentRecord (Input)
example : scanSteps [] = 1 := rfl
example (r : Input) (rs : List Input) :
    scanSteps (r::rs) = LightEFTSpanners.StoredComponentRecord.steps r+2+scanSteps rs := rfl
#eval do
  let mk := fun (i : ℕ) (xs : List ℕ) =>
    ({ id := i, vertices := xs, host := ⟨[],[]⟩ } : Input)
  let empty := mk 999 []
  let one := mk 0 [0]
  let two := mk 999 [0,1]
  let three := mk 999 [0,1,2]
  let decorated : Input := ⟨999,[42,42],⟨[(99,99)],[[ (3,4) ],[],[ (3,4) ]]⟩⟩
  let checks := [
    decide (scanSteps [] = 1),
    decide (scanSteps [empty] = 6),
    decide (scanSteps [one] = 10),
    decide (scanSteps [two] = 18),
    decide (scanSteps [three] = 30),
    decide (scanSteps [mk 0 [0,1,2,3]] = 46),
    decide (scanSteps [mk 0 [9,9]] = 18),
    decide (scanSteps [decorated] = 18),
    decide (scanSteps [mk 999999999999999999999 [100000000000000000000]] = 10),
    decide (scanSteps [empty,empty] = 11),
    decide (scanSteps [empty,one] = 15),
    decide (scanSteps [one,two] = 27),
    decide (scanSteps [one,one,one] = 28),
    decide (scanSteps [two,decorated] = 35),
    decide (scanSteps [empty,one,two,three] = 61),
    decide (scanSteps (List.replicate 16 empty) = 81),
    decide (scanSteps (List.replicate 16 one) = 145),
    decide (scanSteps (List.replicate 16 two) = 273),
    decide (scanSteps [mk 0 (List.replicate 16 7)] = 550),
    decide (scanSteps [mk 0 (List.replicate 32 7)] = 2118)]
  unless checks.all id do throw (IO.userError "Exact component-catalogue scan-count fixtures failed")
  IO.println s!"PASS: {checks.length} complete component-catalogue scan-count fixtures; base one, record steps plus two plus tail, empty/duplicate vertices, repeated records/IDs, arbitrary payloads, huge naturals and long lists"
