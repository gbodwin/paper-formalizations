import LightEFTSpanners.ExecutableVoting
open LightEFTSpanners.ExecutableVoting
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let some c := env.find? `LightEFTSpanners.ExecutableVoting.edges | throwError "edges missing"
  if c.isUnsafe || c.isPartial then throwError "edges is not safe and total"
  if isNoncomputable env c.name then throwError "edges became noncomputable"
  if (env.find? `LightEFTSpanners.ExecutableVoting.edges._unsafe_rec).isSome then
    throwError "Pilot partial companion still exists"
  let .defnInfo v := c | throwError "edges is not a definition"
  unless v.value.getUsedConstants.contains `List.rec do throwError "Explicit List.rec absent"
  if v.value.getUsedConstants.contains c.name then throwError "edges body refers to itself"
  logInfo "PASS: edges safe, total, computable, explicit List.rec, no partial companion"
example {n : ℕ} {J : Type*} [DecidableEq J]
    (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : LightEFTSpanners.SampledGreedy.Tape (Fin n) J)
    (h : ℕ) : edges Q w hw t eligible host tape h [] = Q := rfl
example {n : ℕ} {J : Type*} [DecidableEq J]
    (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : LightEFTSpanners.SampledGreedy.Tape (Fin n) J)
    (h : ℕ) (e : Sym2 (Fin n)) (es : List (Sym2 (Fin n))) :
    edges Q w hw t eligible host tape h (e::es) =
      let E := edges Q w hw t eligible host tape h es
      if h≤(votes Q w hw t eligible host tape E e).card then insert e E else E := rfl
private def fixture (h : ℕ) (l : List (Sym2 (Fin 2))) : Finset (Sym2 (Fin 2)) :=
  edges (J:=Unit) ∅ (fun _ => 0) (by simp) 1
    (fun _ => ∅) (fun _ => ∅) (fun _ _ _ => []) h l
#eval do
  unless (fixture 0 []).card == 0 && (fixture 0 [s(0,1)]).card == 1 &&
      (fixture 1 [s(0,1)]).card == 0 && (fixture 0 [s(0,1),s(0,1)]).card == 1 do
    throw (IO.userError "edges executable fixtures failed")
  IO.println "PASS: empty list, admission, rejection, repeated edge fixtures"
