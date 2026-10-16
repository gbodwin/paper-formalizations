import LightEFTSpanners.StoredDrawLookup
open LightEFTSpanners.StoredDrawLookup
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredDrawLookup.value
  let some c := env.find? name | throwError "value missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "value not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: value safe, total, computable, explicit List.rec, no partial companion"
example (key : ℕ) : value key [] = [] := rfl
example (key i : ℕ) (ds : LightEFTSpanners.StoredVote.Draws) (xs : Bank) :
    value key ((i,ds)::xs) = if key=i then ds else value key xs := rfl
private def a : LightEFTSpanners.StoredVote.Draws := [[(1,2),(3,4)],[],[(5,6),(1,2)]]
private def b : LightEFTSpanners.StoredVote.Draws := [[(2,1)],[(7,7)]]
#eval do
  let checks := [
    decide (value 0 [] = []),
    decide (value 100000000000000000000 [] = []),
    decide (value 7 [(7,a)] = a),
    decide (value 8 [(7,a)] = []),
    decide (value 7 [(7,a),(7,b)] = a),
    decide (value 7 [(7,b),(7,a)] = b),
    decide (value 7 [(7,[]),(7,a)] = []),
    decide (value 7 [(7,[[]]),(7,a)] = [[]]),
    decide (value 7 [(7,[[],[]]),(7,a)] = [[],[]]),
    decide (value 7 [(8,[]),(7,a),(7,b)] = a),
    decide (value 7 [(8,a),(7,[]),(7,b)] = []),
    decide (value 7 [(8,a),(9,b)] = []),
    decide (value 9 [(8,a),(9,b)] = b),
    decide (value 0 [(0,[[(0,0),(0,0)]])] = [[(0,0),(0,0)]]),
    decide (value 1 [(1,[[(2,1),(1,2),(2,1)]])] = [[(2,1),(1,2),(2,1)]]),
    decide (value 2 [(2,[[(1,1)],[],[(3,3)],[]])] = [[(1,1)],[],[(3,3)],[]]),
    decide (value 100000000000000000000 [(0,a),(100000000000000000000,b)] = b),
    decide (value 4 [(4,[[(100000000000000000000,99999999999999999999)]])] = [[(100000000000000000000,99999999999999999999)]]),
    decide (value 7 (List.replicate 16 (8,b) ++ [(7,a)]) = a),
    decide (value 7 ([(7,[])] ++ List.replicate 16 (7,a)) = [])]
  unless checks.all id do throw (IO.userError "Complete draw payload fixtures failed")
  IO.println s!"PASS: {checks.length} complete nested payload fixtures; first match, duplicates, empty matching payload, empty inner draws, exact order, repeated/oriented edges, misses and large keys"
