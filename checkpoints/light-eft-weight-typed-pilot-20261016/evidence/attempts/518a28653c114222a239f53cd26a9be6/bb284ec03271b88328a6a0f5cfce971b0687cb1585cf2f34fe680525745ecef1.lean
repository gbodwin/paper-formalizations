import LightEFTSpanners.StoredOriginalWeightEncoding
open LightEFTSpanners
open StoredOriginalWeightLookup
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredOriginalWeightLookup.weight
  let some c := env.find? name | throwError "weight missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "weight not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: weight safe, total, computable, explicit List.rec, no partial companion"
example {n : ℕ} (e : Sym2 (Fin n)) : weight e [] = 0 := rfl
example {n : ℕ} (e : Sym2 (Fin n)) (p : Fin n × Fin n) (q : ℚ) (rs : TypedBank n) :
    weight e ((p,q)::rs) = if e=s(p.1,p.2) then q else weight e rs := rfl
-- For n=0 no query exists; record the original impossible-input boundary.
example (e : Sym2 (Fin 0)) : False := Fin.elim0 e.out.1
private def a : ℚ := -13/7
private def b : ℚ := 999999999999999999999/11
private def key : Sym2 (Fin 3) := s(0,1)
#eval do
  let checks := [
    decide (weight key [] = 0),
    decide (weight key [((0,1),a)] = a),
    decide (weight key [((1,0),a)] = a),
    decide (weight s((1 : Fin 3),0) [((0,1),a)] = a),
    decide (weight key [((0,1),a),((0,1),b)] = a),
    decide (weight key [((1,0),b),((0,1),a)] = b),
    decide (weight key [((0,1),0),((1,0),a)] = 0),
    decide (weight key [((2,2),a)] = 0),
    decide (weight key [((0,2),b),((1,0),a)] = a),
    decide (weight key [((1,0),a),((0,2),b)] = a),
    decide (weight key [((0,2),a),((2,0),b),((1,1),a)] = 0),
    decide (weight key [((2,0),0),((0,1),a),((1,0),b)] = a),
    decide (weight s((2 : Fin 3),2) [((0,1),b),((2,2),a)] = a),
    decide (weight s((0 : Fin 1),0) [((0,0),(-1/3))] = -1/3),
    decide (weight key [((1,0),(-5/2)),((0,1),a)] = -5/2),
    decide (weight s((0 : Fin 1),0) [] = 0),
    decide (weight s((0 : Fin 1),0) [((0,0),0),((0,0),b)] = 0),
    decide (weight s((0 : Fin 3),0) [((0,1),a)] = 0),
    decide (weight key (List.replicate 64 ((2,2),a)) = 0),
    decide (weight key (List.replicate 64 ((2,2),0) ++ [((1,0),b),((0,1),a)]) = b)]
  unless checks.all id do throw (IO.userError "Exact typed rational payload fixtures failed")
  IO.println s!"PASS: {checks.length} exact-payload fixtures: absent zero, zero/negative first matches, arbitrary signed rationals, Sym2 reversal, duplicate priority, singleton loops and long prefixes; n=0 impossibility checked"
