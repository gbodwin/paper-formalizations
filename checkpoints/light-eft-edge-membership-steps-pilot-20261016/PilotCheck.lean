import LightEFTSpanners.StoredEdgeMembership
open LightEFTSpanners.StoredEdges
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredEdges.steps
  let some c := env.find? name | throwError "steps missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "steps not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: steps safe, total, computable, explicit List.rec, no partial companion"
example (q : Edge) : steps q [] = 1 := rfl
example (q e : Edge) (es : List Edge) : steps q (e::es) = (if same q e then 1 else steps q es+1) := rfl
#eval do
  let checks := [
    decide (steps (0,1) [] = 1),
    decide (steps (999,999) [] = 1),
    decide (steps (0,1) [(0,1)] = 1),
    decide (steps (0,1) [(1,0)] = 1),
    decide (steps (0,0) [(0,0)] = 1),
    decide (steps (0,0) [(0,1)] = 2),
    decide (steps (0,1) [(0,0)] = 2),
    decide (steps (0,1) [(0,2)] = 2),
    decide (steps (1,0) [(0,1)] = 1),
    decide (steps (0,1) [(9,8),(1,0)] = 2),
    decide (steps (0,1) [(9,8),(7,6),(0,1)] = 3),
    decide (steps (0,1) [(9,8),(7,6)] = 3),
    decide (steps (0,1) [(0,1),(1,0),(0,1)] = 1),
    decide (steps (0,1) [(9,8),(9,8),(1,0),(0,1)] = 3),
    decide (steps (100000000000000000000,1) [(1,100000000000000000000)] = 1),
    decide (steps (100000000000000000000,1) [(1,2),(100000000000000000000,1)] = 2),
    decide (steps (0,1) (List.replicate 32 (1,0)) = 1),
    decide (steps (0,1) (List.replicate 32 (9,8)) = 33),
    decide (steps (0,1) (List.replicate 32 (9,8) ++ [(1,0)]) = 33),
    decide (steps (9,9) [(0,0),(1,1),(9,9),(9,9)] = 3)]
  unless checks.all id do throw (IO.userError "Exact endpoint-pair step-count fixtures failed")
  IO.println s!"PASS: {checks.length} complete endpoint-pair count fixtures; empty, direct/reverse matching, loops, absent/shared endpoints, duplicates, huge naturals and long lists"
