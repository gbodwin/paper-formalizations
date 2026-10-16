import LightEFTSpanners.StoredDrawLookupEncoding
open LightEFTSpanners
open StoredDrawLookup
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredDrawLookup.typedValue
  let some c := env.find? name | throwError "typedValue missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "typedValue not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: typedValue safe, total, computable, explicit List.rec, no partial companion"
example {n : ℕ} (key : ℕ) : typedValue (n:=n) key [] = [] := rfl
example {n : ℕ} (key i : ℕ) (ds : List (List (Fin n × Fin n))) (xs : TypedBank n) :
    typedValue key ((i,ds)::xs) = if key=i then ds else typedValue key xs := rfl
private def a : List (List (Fin 3 × Fin 3)) := [[],[(0,1),(1,0),(2,2),(0,1)],[(2,0)],[]]
private def b : List (List (Fin 3 × Fin 3)) := [[(0,0)]]
private def huge : ℕ := 100000000000000000000
#eval do
  let checks := [
    decide (typedValue (n:=3) 0 [] = []),
    decide (typedValue 0 [(0,a)] = a),
    decide (typedValue 7 [(7,a)] = a),
    decide (typedValue 7 [(7,a),(7,b)] = a),
    decide (typedValue 7 [(7,b),(7,a)] = b),
    decide (typedValue 7 [(7,[]),(7,a)] = []),
    decide (typedValue 7 [(7,[[]]),(7,a)] = [[]]),
    decide (typedValue 7 [(0,b),(7,a),(7,b)] = a),
    decide (typedValue 7 [(7,a),(0,b)] = a),
    decide (typedValue 7 [(0,a),(6,b),(8,a)] = []),
    decide (typedValue huge [(0,b),(huge,a),(huge,b)] = a),
    decide (typedValue (huge+1) [(huge,a),(0,b)] = []),
    decide (typedValue 0 [(huge,a),(0,b),(0,a)] = b),
    decide (typedValue (n:=1) huge [(huge,[[],[(0,0),(0,0)]])]=( [[],[(0,0),(0,0)]] )),
    decide (typedValue (n:=0) 0 [] = []),
    decide (typedValue (n:=0) huge [(huge,[[],[]])] = [[],[]]),
    decide (typedValue (n:=0) huge [(huge,[]),(huge,[[]])] = []),
    decide (typedValue (n:=0) (huge+1) [(huge,[[],[]])] = [])]
  unless checks.all id do throw (IO.userError "Complete nested draw fixtures failed")
  IO.println s!"PASS: {checks.length} full-payload fixtures: arbitrary natural keys, zero/large/missing keys, first duplicate priority, empty first match, nested order/multiplicity, loops/reversals and actual zero/singleton-vertex inputs"
