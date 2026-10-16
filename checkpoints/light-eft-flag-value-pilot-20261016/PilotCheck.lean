import LightEFTSpanners.StoredFlagSample
open LightEFTSpanners.StoredFlagSample
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredFlagSample.value
  let some c := env.find? name | throwError "value missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "value not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: value safe, total, computable, explicit List.rec, no partial companion"
example : value [] = [] := rfl
example (e : LightEFTSpanners.StoredEdges.Edge) (b : Bool) (xs : Input) :
    value ((e,b)::xs) = if b then e::value xs else value xs := rfl
#eval do
  let checks := [
    decide (value [] = []),
    decide (value [((0,1),false)] = []),
    decide (value [((0,1),true)] = [(0,1)]),
    decide (value [((0,0),true)] = [(0,0)]),
    decide (value [((42,42),true),((0,0),false)] = [(42,42)]),
    decide (value [((3,2),true),((2,3),true)] = [(3,2),(2,3)]),
    decide (value [((1,2),true),((1,2),true)] = [(1,2),(1,2)]),
    decide (value [((1,2),false),((1,2),true)] = [(1,2)]),
    decide (value [((1,2),true),((1,2),false)] = [(1,2)]),
    decide (value [((4,5),false),((8,9),false),((1,1),false)] = []),
    decide (value [((9,0),true),((2,2),false),((3,1),true),((9,0),true)] = [(9,0),(3,1),(9,0)]),
    decide (value [((100000000000000000000,0),true),((0,100000000000000000000),true)] =
      [(100000000000000000000,0),(0,100000000000000000000)]),
    decide (value [((100000000000000000000,100000000000000000000),false)] = []),
    decide (value [((7,8),true),((0,0),true),((8,7),true),((7,8),true)] = [(7,8),(0,0),(8,7),(7,8)]),
    decide (value [((0,1),false),((1,0),true),((0,1),false),((1,0),true)] = [(1,0),(1,0)])]
  unless checks.all id do throw (IO.userError "Full-list flag value fixtures failed")
  IO.println s!"PASS: {checks.length} full-list fixtures: empty, false/true flags, duplicate multiplicity, order, loops, reversed pairs, mixed flags and unrestricted large natural endpoints"
