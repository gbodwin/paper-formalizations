import LightEFTSpanners.StoredHostPreparation
open LightEFTSpanners.StoredHostPreparation
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredHostPreparation.scanSteps
  let some c := env.find? name | throwError "scanSteps missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "scanSteps not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: scanSteps safe, total, computable, explicit List.rec, no partial companion"
example (e : LightEFTSpanners.StoredEdges.Edge) : scanSteps e [] = 1 := rfl
example (e : LightEFTSpanners.StoredEdges.Edge) (r : Record) (rs : List Record) :
    scanSteps e (r::rs) = LightEFTSpanners.StoredEdges.steps e r.eligibleEdges+2+scanSteps e rs := rfl
#eval do
  let mk := fun (i : ℕ) (xs : List LightEFTSpanners.StoredEdges.Edge) =>
    ({ id := i, eligibleEdges := xs, host := ⟨[],[]⟩ } : Record)
  let empty := mk 999 []
  let matched := mk 0 [(0,1)]
  let absent := mk 999 [(9,8)]
  let absentTwo := mk 999 [(9,8),(7,6)]
  let decorated : Record := ⟨999,[(1,0)],⟨[(99,99)],[[ (3,4) ],[],[ (3,4) ]]⟩⟩
  let checks := [
    decide (scanSteps (0,1) [] = 1),
    decide (scanSteps (100000000000000000000,100000000000000000000) [] = 1),
    decide (scanSteps (0,1) [empty] = 4),
    decide (scanSteps (0,1) [matched] = 4),
    decide (scanSteps (0,1) [decorated] = 4),
    decide (scanSteps (0,1) [absent] = 5),
    decide (scanSteps (0,1) [mk 7 [(9,8),(1,0)]] = 5),
    decide (scanSteps (0,1) [absentTwo] = 6),
    decide (scanSteps (0,0) [mk 7 [(0,0)]] = 4),
    decide (scanSteps (0,1) [mk 7 [(0,0)]] = 5),
    decide (scanSteps (0,1) [mk 0 [(0,1),(1,0),(0,1)]] = 4),
    decide (scanSteps (0,1) [mk 6 [(9,8),(7,6),(0,1)]] = 6),
    decide (scanSteps (0,1) [empty,empty] = 7),
    decide (scanSteps (0,1) [matched,absent] = 8),
    decide (scanSteps (0,1) [matched,matched,matched] = 10),
    decide (scanSteps (0,1) [empty,absentTwo,decorated] = 12),
    decide (scanSteps (100000000000000000000,1) [mk 99999999999999999999 [(1,100000000000000000000)]] = 4),
    decide (scanSteps (0,1) (List.replicate 16 empty) = 49),
    decide (scanSteps (0,1) (List.replicate 16 absent) = 65),
    decide (scanSteps (0,1) (List.replicate 16 (mk 0 (List.replicate 32 (9,8) ++ [(1,0)]))) = 561)]
  unless checks.all id do throw (IO.userError "Exact host-preparation scan-count fixtures failed")
  IO.println s!"PASS: {checks.length} complete host-preparation scan-count fixtures; base one, membership plus two plus tail, direct/reverse pairs, loops, absent edges, duplicate records/IDs, arbitrary payloads, huge naturals and long lists"
