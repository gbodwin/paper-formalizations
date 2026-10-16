import LightEFTSpanners.StoredVertexMembership
open LightEFTSpanners.StoredVertexMembership
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredVertexMembership.steps
  let some c := env.find? name | throwError "steps missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "steps not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: steps safe, total, computable, explicit List.rec, no partial companion"
example (v : ℕ) : steps v [] = 1 := rfl
example (v x : ℕ) (xs : List ℕ) : steps v (x::xs) = (if v=x then 1 else steps v xs+1) := rfl
#eval do
  let checks := [
    decide (steps 0 [] = 1),
    decide (steps 999 [] = 1),
    decide (steps 0 [0] = 1),
    decide (steps 0 [1] = 2),
    decide (steps 1 [0] = 2),
    decide (steps 0 [0,9,8] = 1),
    decide (steps 0 [1,0] = 2),
    decide (steps 0 [1,2,0] = 3),
    decide (steps 0 [1,2,3] = 4),
    decide (steps 2 [0,1,2,3] = 3),
    decide (steps 0 [0,0,0] = 1),
    decide (steps 0 [1,1,0,0] = 3),
    decide (steps 0 [1,1,1,1] = 5),
    decide (steps 100000000000000000000 [100000000000000000000] = 1),
    decide (steps 100000000000000000000 [1,2,100000000000000000000] = 3),
    decide (steps 100000000000000000000 [1,2,3] = 4),
    decide (steps 0 (List.replicate 32 0) = 1),
    decide (steps 0 (List.replicate 32 1) = 33),
    decide (steps 0 (List.replicate 32 1 ++ [0,9]) = 33),
    decide (steps 0 (0::List.replicate 32 1) = 1)]
  unless checks.all id do throw (IO.userError "Exact membership step-count fixtures failed")
  IO.println s!"PASS: {checks.length} complete natural membership-count fixtures; empty count one, matching head one, first match, absence, duplicates, huge naturals and long tails"
