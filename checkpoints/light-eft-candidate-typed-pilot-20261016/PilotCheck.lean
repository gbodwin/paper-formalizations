import LightEFTSpanners.StoredCandidateDrawEncoding
open LightEFTSpanners
open StoredCandidateDrawLookup
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredCandidateDrawLookup.typedValue
  let some c := env.find? name | throwError "typedValue missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "typedValue not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: typedValue safe, total, computable, explicit List.rec, no partial companion"
example {n : ℕ} (e : Sym2 (Fin n)) : typedValue e [] = [] := rfl
example {n : ℕ} (e : Sym2 (Fin n)) (p : Fin n × Fin n)
    (ds : StoredDrawLookup.TypedBank n) (rs : TypedBank n) :
    typedValue e ((p,ds)::rs) = if e=s(p.1,p.2) then ds else typedValue e rs := rfl
-- n=0 has no query key; this is the original type's impossible-input case.
example (e : Sym2 (Fin 0)) : False := Fin.elim0 e.out.1
private def a : StoredDrawLookup.TypedBank 3 :=
  [(7,[[],[(0,1),(1,0),(2,2),(0,1)]]),(7,[]),(100000000000000000000,[[(2,0)],[]])]
private def b : StoredDrawLookup.TypedBank 3 := [(0,[[(2,0)]])]
private def key : Sym2 (Fin 3) := s(0,1)
#eval do
  let checks := [
    decide (typedValue key [] = []),
    decide (typedValue key [((0,1),a)] = a),
    decide (typedValue key [((1,0),a)] = a),
    decide (typedValue s((1 : Fin 3),0) [((0,1),a)] = a),
    decide (typedValue key [((0,1),a),((0,1),b)] = a),
    decide (typedValue key [((1,0),b),((0,1),a)] = b),
    decide (typedValue key [((0,1),[]),((1,0),a)] = []),
    decide (typedValue key [((2,2),a)] = []),
    decide (typedValue key [((0,2),b),((1,0),a)] = a),
    decide (typedValue key [((1,0),a),((0,2),b)] = a),
    decide (typedValue key [((0,2),a),((2,0),b),((1,1),a)] = []),
    decide (typedValue key [((2,0),[]),((0,1),a),((1,0),b)] = a),
    decide (typedValue s((2 : Fin 3),2) [((0,1),b),((2,2),a)] = a),
    decide (typedValue s((0 : Fin 1),0) [((0,0),[(99,[[],[(0,0),(0,0)]])])] = [(99,[[],[(0,0),(0,0)]])]),
    decide (typedValue key [((1,0),[(5,[])]),((0,1),a)] = [(5,[])]),
    decide (typedValue key [((0,1),b),((1,0),a),((0,1),[])] = b)]
  unless checks.all id do throw (IO.userError "Complete nested payload fixtures failed")
  IO.println s!"PASS: {checks.length} full-payload fixtures: empty/missing, first-match duplicates, reversed keys, empty first payload, unrelated prefixes, loops, singleton vertices and unrestricted nested payloads"
