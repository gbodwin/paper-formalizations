import LightEFTSpanners.StoredComponentBank
open LightEFTSpanners.StoredComponentBank
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredComponentBank.scanSteps
  let some c := env.find? name | throwError "scanSteps missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "scanSteps not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: scanSteps safe, total, computable, explicit List.rec, no partial companion"
open LightEFTSpanners.StoredComponentCandidate (Input)
example (W : LightEFTSpanners.StoredRecords.Weights) : scanSteps W [] = 1 := rfl
example (W : LightEFTSpanners.StoredRecords.Weights) (r : Input) (rs : List Input) :
    scanSteps W (r::rs) = LightEFTSpanners.StoredComponentCandidate.steps W r+2+scanSteps W rs := rfl
#eval do
  let component := fun (i : ℕ) (xs : List ℕ) =>
    ({ id := i, vertices := xs, host := ⟨[],[]⟩ } : LightEFTSpanners.StoredComponentRecord.Input)
  let mk := fun (edge : LightEFTSpanners.StoredEdges.Edge) (cs : List LightEFTSpanners.StoredComponentRecord.Input) =>
    ({ edge := edge, components := cs } : Input)
  let empty := mk (0,0) []
  let two := component 9 [0,1]
  let decorated : LightEFTSpanners.StoredComponentRecord.Input :=
    ⟨999999999999999999999,[0,1],⟨[(99,99)],[[ (3,4) ],[],[ (3,4) ]]⟩⟩
  let W : LightEFTSpanners.StoredRecords.Weights := [[],[-3/2,7]]
  let checks := [
    decide (scanSteps [] [] = 1),
    decide (scanSteps W [] = 1),
    decide (scanSteps [] [empty] = 14),
    decide (scanSteps [[-3/2]] [empty] = 15),
    decide (scanSteps [[]] [mk (0,1) []] = 15),
    decide (scanSteps W [mk (1,1) []] = 17),
    decide (scanSteps W [mk (100000000000000000000,100000000000000000000) []] = 16),
    decide (scanSteps [] [mk (0,1) [component 9 []]] = 23),
    decide (scanSteps [] [mk (0,0) [component 9 [0]]] = 30),
    decide (scanSteps [] [mk (0,1) [component 9 [0]]] = 28),
    decide (scanSteps [] [mk (0,1) [two]] = 39),
    decide (scanSteps [] [mk (1,0) [two]] = 39),
    decide (scanSteps [] [mk (1,1) [two]] = 41),
    decide (scanSteps [] [mk (9,8) [two]] = 39),
    decide (scanSteps [] [mk (0,0) [component 9 [0,0]]] = 38),
    decide (scanSteps [] [mk (0,1) [decorated]] = 39),
    decide (scanSteps W [mk (1,1) [two]] = 44),
    decide (scanSteps [] [empty,mk (0,1) [two],empty] = 65),
    decide (scanSteps [] (List.replicate 16 empty) = 209),
    decide (scanSteps [] [mk (0,1) (List.replicate 16 (component 9 []))] = 158)]
  unless checks.all id do throw (IO.userError "Exact component-bank scan-count fixtures failed")
  IO.println s!"PASS: {checks.length} complete component-bank scan-count fixtures; arbitrary ragged/negative weights, base one, candidate steps plus two plus tail, loops/reverse pairs, repeated IDs/records, arbitrary payloads, huge naturals and long lists"
