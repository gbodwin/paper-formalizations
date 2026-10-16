import LightEFTSpanners.StoredDrawLookup
open LightEFTSpanners.StoredDrawLookup
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredDrawLookup.steps
  let some c := env.find? name | throwError "steps missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "steps not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: steps safe, total, computable, explicit List.rec, no partial companion"
example (key : ℕ) : steps key [] = 1 := rfl
example (key i : ℕ) (ds : LightEFTSpanners.StoredVote.Draws) (xs : Bank) :
    steps key ((i,ds)::xs) = if key=i then 1 else 1+steps key xs := rfl
private def a : LightEFTSpanners.StoredVote.Draws := [[(1,2),(3,4)],[],[(5,6),(1,2)]]
private def b : LightEFTSpanners.StoredVote.Draws := [[(2,1)],[(7,7)]]
#eval do
  let checks := [
    decide (steps 0 [] = 1),
    decide (steps 100000000000000000000 [] = 1),
    decide (steps 7 [(7,a)] = 1),
    decide (steps 8 [(7,a)] = 2),
    decide (steps 7 [(7,a),(7,b)] = 1),
    decide (steps 7 [(7,b),(7,a)] = 1),
    decide (steps 7 [(7,[]),(7,a)] = 1),
    decide (steps 7 [(7,[[]]),(7,a)] = 1),
    decide (steps 7 [(7,[[],[]]),(7,a)] = 1),
    decide (steps 7 [(8,[]),(7,a),(7,b)] = 2),
    decide (steps 7 [(8,a),(7,[]),(7,b)] = 2),
    decide (steps 7 [(8,a),(9,b)] = 3),
    decide (steps 9 [(8,a),(9,b)] = 2),
    decide (steps 0 [(0,[[(0,0),(0,0)]])] = 1),
    decide (steps 7 [(8,a),(9,b),(7,[]),(7,a)] = 3),
    decide (steps 100000000000000000000 [(0,a),(100000000000000000000,b)] = 2),
    decide (steps 7 (List.replicate 16 (8,b) ++ [(7,a)]) = 17),
    decide (steps 7 (List.replicate 16 (8,b)) = 17),
    decide (steps 7 ([(7,[])] ++ List.replicate 16 (7,a)) = 1),
    decide (steps 7 [(7,List.replicate 32 [(1,2),(2,1)])] = 1)]
  unless checks.all id do throw (IO.userError "Exact first-match count fixtures failed")
  IO.println s!"PASS: {checks.length} complete natural transition-count fixtures; empty bank, first match, duplicates, empty matching payload, nonmatches, final halt, large keys and payload independence"
