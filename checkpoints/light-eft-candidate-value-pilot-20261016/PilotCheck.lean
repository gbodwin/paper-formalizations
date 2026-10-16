import LightEFTSpanners.StoredCandidateDrawLookup
open LightEFTSpanners
open StoredCandidateDrawLookup
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredCandidateDrawLookup.value
  let some c := env.find? name | throwError "value missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "value not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: value safe, total, computable, explicit List.rec, no partial companion"
example (key : StoredEdges.Edge) : value key [] = [] := rfl
example (key i : StoredEdges.Edge) (ds : StoredDrawLookup.Bank) (rs : Bank) :
    value key ((i,ds)::rs) = if StoredEdges.same key i then ds else value key rs := rfl
private def a : StoredDrawLookup.Bank :=
  [(7,[[],[(0,1),(1,0),(2,2),(0,1)]]),(7,[]),(100000000000000000000,[[(2,0)],[]])]
private def b : StoredDrawLookup.Bank := [(0,[[(2,0)]])]
private def key : StoredEdges.Edge := (0,1)
#eval do
  let checks := [
    decide (value key [] = []),
    decide (value key [((0,1),a)] = a),
    decide (value key [((1,0),a)] = a),
    decide (value (1,0) [((0,1),a)] = a),
    decide (value key [((0,1),a),((0,1),b)] = a),
    decide (value key [((1,0),b),((0,1),a)] = b),
    decide (value key [((0,1),[]),((1,0),a)] = []),
    decide (value key [((2,2),a)] = []),
    decide (value key [((0,2),b),((1,0),a)] = a),
    decide (value key [((1,0),a),((0,2),b)] = a),
    decide (value key [((0,2),a),((2,0),b),((1,1),a)] = []),
    decide (value key [((2,0),[]),((0,1),a),((1,0),b)] = a),
    decide (value (2,2) [((0,1),b),((2,2),a)] = a),
    decide (value (0,0) [((0,0),[(99,[[],[(0,0),(0,0)]])])] = [(99,[[],[(0,0),(0,0)]])]),
    decide (value key [((1,0),[(5,[])]),((0,1),a)] = [(5,[])]),
    decide (value key [((0,1),b),((1,0),a),((0,1),[])] = b),
    decide (value (100000000000000000000,7) [((7,100000000000000000000),a)] = a),
    decide (value (7,100000000000000000000) [((7,100000000000000000000),[]),((100000000000000000000,7),a)] = []),
    decide (value (0,0) [((0,1),a)] = [])]
  unless checks.all id do throw (IO.userError "Complete nested payload fixtures failed")
  IO.println s!"PASS: {checks.length} full-payload fixtures: empty/missing, first-match duplicates, reversed keys, empty first payload, unrelated prefixes, loops, arbitrary natural endpoints and unrestricted nested payloads"
