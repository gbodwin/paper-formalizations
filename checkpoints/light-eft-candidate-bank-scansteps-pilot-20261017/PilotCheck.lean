import LightEFTSpanners.StoredCandidateBankPreparation
open LightEFTSpanners.StoredCandidateBankPreparation
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredCandidateBankPreparation.scanSteps
  let some c := env.find? name | throwError "scanSteps missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "scanSteps not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: scanSteps safe, total, computable, explicit List.rec, no partial companion"
open LightEFTSpanners.StoredCandidatePreparation (Input)
example (W : LightEFTSpanners.StoredRecords.Weights) : scanSteps W [] = 1 := rfl
example (W : LightEFTSpanners.StoredRecords.Weights) (r : Input) (rs : List Input) :
    scanSteps W (r::rs) = LightEFTSpanners.StoredCandidatePreparation.steps W r+2+scanSteps W rs := rfl
#eval do
  let host := fun (i : ℕ) (es : List LightEFTSpanners.StoredEdges.Edge) =>
    ({ id := i, eligibleEdges := es, host := ⟨[],[]⟩ } : LightEFTSpanners.StoredHostPreparation.Record)
  let mk := fun (edge : LightEFTSpanners.StoredEdges.Edge) (hs : List LightEFTSpanners.StoredHostPreparation.Record) =>
    ({ edge := edge, catalogue := hs } : Input)
  let empty := mk (0,0) []
  let matched := host 9 [(0,1)]
  let decorated : LightEFTSpanners.StoredHostPreparation.Record :=
    ⟨999999999999999999999,[(1,0)],⟨[(99,99)],[[ (3,4) ],[],[ (3,4) ]]⟩⟩
  let W : LightEFTSpanners.StoredRecords.Weights := [[],[-3/2,7]]
  let checks := [
    decide (scanSteps [] [] = 1),
    decide (scanSteps W [] = 1),
    decide (scanSteps [] [empty] = 11),
    decide (scanSteps [[-3/2]] [empty] = 12),
    decide (scanSteps [[]] [mk (0,1) []] = 12),
    decide (scanSteps W [mk (1,1) []] = 14),
    decide (scanSteps W [mk (100000000000000000000,100000000000000000000) []] = 13),
    decide (scanSteps [] [mk (0,1) [host 9 []]] = 14),
    decide (scanSteps [] [mk (0,1) [matched]] = 17),
    decide (scanSteps [] [mk (1,0) [matched]] = 17),
    decide (scanSteps [] [mk (0,0) [host 9 [(0,0)]]] = 17),
    decide (scanSteps [] [mk (9,8) [matched]] = 15),
    decide (scanSteps [] [mk (0,1) [host 9 [(9,8),(0,1)]]] = 18),
    decide (scanSteps [] [mk (0,1) [host 9 [(0,1),(1,0),(0,1)]]] = 17),
    decide (scanSteps [] [mk (0,1) [decorated]] = 17),
    decide (scanSteps W [mk (1,1) [host 9 [(1,1)]]] = 20),
    decide (scanSteps [] [empty,mk (0,1) [matched],empty] = 37),
    decide (scanSteps [] (List.replicate 16 empty) = 161),
    decide (scanSteps [] [mk (0,1) (List.replicate 16 matched)] = 107),
    decide (scanSteps [] [mk (0,1) [host 9 (List.replicate 32 (9,8) ++ [(1,0)])]] = 49)]
  unless checks.all id do throw (IO.userError "Exact candidate-bank scan-count fixtures failed")
  IO.println s!"PASS: {checks.length} complete candidate-bank scan-count fixtures; arbitrary ragged/negative weights, base one, preparation steps plus two plus tail, loops/reverse pairs, duplicate eligibility/IDs/records, arbitrary payloads, huge naturals and long lists"
