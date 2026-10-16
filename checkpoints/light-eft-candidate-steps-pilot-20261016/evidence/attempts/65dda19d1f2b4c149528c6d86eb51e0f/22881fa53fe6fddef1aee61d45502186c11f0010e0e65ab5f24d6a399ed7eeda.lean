import LightEFTSpanners.StoredCandidateDrawLookup
open LightEFTSpanners
open StoredCandidateDrawLookup
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredCandidateDrawLookup.steps
  let some c := env.find? name | throwError "steps missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "steps not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: steps safe, total, computable, explicit List.rec, no partial companion"
example (key : StoredEdges.Edge) : steps key [] = 1 := rfl
example (key i : StoredEdges.Edge) (ds : StoredDrawLookup.Bank) (rs : Bank) :
    steps key ((i,ds)::rs) = if StoredEdges.same key i then 1 else 1+steps key rs := rfl
private def a : StoredDrawLookup.Bank :=
  [(7,[[],[(0,1),(1,0),(2,2),(0,1)]]),(7,[]),(100000000000000000000,[[(2,0)],[]])]
private def b : StoredDrawLookup.Bank := [(0,[[(2,0)]])]
private def key : StoredEdges.Edge := (0,1)
#eval do
  let checks := [
    decide (steps key [] = 1),
    decide (steps key [((0,1),a)] = 1),
    decide (steps key [((1,0),a)] = 1),
    decide (steps (1,0) [((0,1),a)] = 1),
    decide (steps key [((0,1),a),((0,1),b)] = 1),
    decide (steps key [((1,0),[]),((0,1),a)] = 1),
    decide (steps key [((2,2),a)] = 2),
    decide (steps key [((0,2),b),((1,0),a)] = 2),
    decide (steps key [((1,0),a),((0,2),b)] = 1),
    decide (steps key [((0,2),a),((2,0),b),((1,1),a)] = 4),
    decide (steps key [((2,0),[]),((0,1),a),((1,0),b)] = 2),
    decide (steps (2,2) [((0,1),b),((2,2),a)] = 2),
    decide (steps (0,0) [((0,0),[(99,[[],[(0,0),(0,0)]])])] = 1),
    decide (steps key [((1,0),[(5,[])]),((0,1),a)] = 1),
    decide (steps (100000000000000000000,7) [((7,100000000000000000000),a)] = 1),
    decide (steps (7,100000000000000000000) [((0,0),[]),((100000000000000000000,7),a)] = 2),
    decide (steps (0,0) [((0,1),a)] = 2),
    decide (steps key [((2,0),a),((2,2),b),((1,0),[])] = 3),
    decide (steps key (List.replicate 64 ((2,2),a)) = 65),
    decide (steps key (List.replicate 64 ((2,2),[]) ++ [((1,0),a)]) = 65)]
  unless checks.all id do throw (IO.userError "Exact step-count fixtures failed")
  IO.println s!"PASS: {checks.length} exact-count fixtures: nil terminal step, first match, reversed keys, duplicate priority, missing keys, loops, large natural endpoints, payload independence and long prefixes"
