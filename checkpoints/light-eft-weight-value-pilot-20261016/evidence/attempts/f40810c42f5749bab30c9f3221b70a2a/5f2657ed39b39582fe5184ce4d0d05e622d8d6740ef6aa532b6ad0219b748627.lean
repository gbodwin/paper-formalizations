import LightEFTSpanners.StoredOriginalWeightLookup
open LightEFTSpanners
open StoredOriginalWeightLookup
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredOriginalWeightLookup.value
  let some c := env.find? name | throwError "value missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "value not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: value safe, total, computable, explicit List.rec, no partial companion"
example (key : StoredEdges.Edge) : value key [] = 0 := rfl
example (key i : StoredEdges.Edge) (q : ℚ) (rs : Bank) :
    value key ((i,q)::rs) = if StoredEdges.same key i then q else value key rs := rfl
private def a : ℚ := -13/7
private def b : ℚ := 999999999999999999999/11
private def key : StoredEdges.Edge := (0,1)
#eval do
  let checks := [
    decide (value key [] = 0),
    decide (value key [((0,1),a)] = a),
    decide (value key [((1,0),a)] = a),
    decide (value (1,0) [((0,1),a)] = a),
    decide (value key [((0,1),a),((0,1),b)] = a),
    decide (value key [((1,0),b),((0,1),a)] = b),
    decide (value key [((0,1),0),((1,0),a)] = 0),
    decide (value key [((2,2),a)] = 0),
    decide (value key [((0,2),b),((1,0),a)] = a),
    decide (value key [((1,0),a),((0,2),b)] = a),
    decide (value key [((0,2),a),((2,0),b),((1,1),a)] = 0),
    decide (value key [((2,0),0),((0,1),a),((1,0),b)] = a),
    decide (value (2,2) [((0,1),b),((2,2),a)] = a),
    decide (value (0,0) [((0,0),(-1/3))] = -1/3),
    decide (value key [((1,0),(-5/2)),((0,1),a)] = -5/2),
    decide (value (100000000000000000000,7) [((7,100000000000000000000),a)] = a),
    decide (value (7,100000000000000000000) [((7,100000000000000000000),0),((100000000000000000000,7),b)] = 0),
    decide (value (0,0) [((0,1),a)] = 0),
    decide (value key (List.replicate 64 ((2,2),a)) = 0),
    decide (value key (List.replicate 64 ((2,2),0) ++ [((1,0),b),((0,1),a)]) = b)]
  unless checks.all id do throw (IO.userError "Exact rational payload fixtures failed")
  IO.println s!"PASS: {checks.length} exact-payload fixtures: absent zero, zero/negative first matches, arbitrary signed rationals, fractions, reversed keys, duplicate priority, loops, large natural endpoints and long prefixes"
