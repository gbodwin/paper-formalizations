import LightEFTSpanners.StoredEdgeMembership
open LightEFTSpanners.StoredEdges
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredEdges.contains
  let some c := env.find? name | throwError "contains missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "contains not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: contains safe, total, computable, explicit List.rec, no partial companion"
example (q : Edge) : contains q [] = false := rfl
example (q e : Edge) (es : List Edge) : contains q (e::es) = (if same q e then true else contains q es) := rfl
#eval do
  let checks := [
    decide (contains (0,1) [] = false),
    decide (contains (999,999) [] = false),
    decide (contains (0,1) [(0,1)] = true),
    decide (contains (0,1) [(1,0)] = true),
    decide (contains (0,0) [(0,0)] = true),
    decide (contains (0,0) [(0,1)] = false),
    decide (contains (0,1) [(0,0)] = false),
    decide (contains (0,1) [(0,2)] = false),
    decide (contains (1,0) [(0,1)] = true),
    decide (contains (0,1) [(9,8),(1,0)] = true),
    decide (contains (0,1) [(9,8),(7,6),(0,1)] = true),
    decide (contains (0,1) [(9,8),(7,6)] = false),
    decide (contains (0,1) [(0,1),(1,0),(0,1)] = true),
    decide (contains (0,1) [(9,8),(9,8),(1,0),(0,1)] = true),
    decide (contains (100000000000000000000,1) [(1,100000000000000000000)] = true),
    decide (contains (100000000000000000000,1) [(1,2),(100000000000000000000,1)] = true),
    decide (contains (0,1) (List.replicate 32 (1,0)) = true),
    decide (contains (0,1) (List.replicate 32 (9,8)) = false),
    decide (contains (0,1) (List.replicate 32 (9,8) ++ [(1,0)]) = true),
    decide (contains (9,9) [(0,0),(1,1),(9,9),(9,9)] = true)]
  unless checks.all id do throw (IO.userError "Exact endpoint-pair Boolean fixtures failed")
  IO.println s!"PASS: {checks.length} exact endpoint-pair Boolean fixtures; empty, direct/reverse matching, loops, absent/shared endpoints, duplicates, huge naturals and long lists"
