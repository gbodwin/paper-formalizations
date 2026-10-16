import LightEFTSpanners.StoredVertexMembership
open LightEFTSpanners.StoredVertexMembership
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredVertexMembership.contains
  let some c := env.find? name | throwError "contains missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "contains not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: contains safe, total, computable, explicit List.rec, no partial companion"
example (v : ℕ) : contains v [] = false := rfl
example (v x : ℕ) (xs : List ℕ) : contains v (x::xs) = (if v=x then true else contains v xs) := rfl
#eval do
  let checks := [
    decide (contains 0 [] = false),
    decide (contains 999 [] = false),
    decide (contains 0 [0] = true),
    decide (contains 0 [1] = false),
    decide (contains 1 [0] = false),
    decide (contains 0 [0,9,8] = true),
    decide (contains 0 [1,0] = true),
    decide (contains 0 [1,2,0] = true),
    decide (contains 0 [1,2,3] = false),
    decide (contains 2 [3,2,1,0] = true),
    decide (contains 0 [0,0,0] = true),
    decide (contains 0 [1,1,0,0] = true),
    decide (contains 0 [1,1,1,1] = false),
    decide (contains 100000000000000000000 [100000000000000000000] = true),
    decide (contains 100000000000000000000 [1,2,100000000000000000000] = true),
    decide (contains 100000000000000000000 [1,2,3] = false),
    decide (contains 0 (List.replicate 32 0) = true),
    decide (contains 0 (List.replicate 32 1) = false),
    decide (contains 0 (List.replicate 32 1 ++ [0,9]) = true),
    decide (contains 0 (0::List.replicate 32 1) = true)]
  unless checks.all id do throw (IO.userError "Exact membership Boolean fixtures failed")
  IO.println s!"PASS: {checks.length} exact Boolean membership fixtures; empty false, matching head true, tail results, absence, duplicates, huge naturals and long tails"
