import LightEFTSpanners.StoredCandidateTrace
open LightEFTSpanners.StoredCandidates
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredCandidates.work
  let some c := env.find? name | throwError "work missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "work not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: work safe, total, computable, explicit List.rec, no partial companion"
example {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (h : ℕ) :
    work Q w h [] E = 1 := rfl
example {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (h : ℕ)
    (R : TypedInput n) (rs : List (TypedInput n)) :
    work Q w h (R::rs) E = (R.hosts.map fun H => LightEFTSpanners.StoredHosts.hostBound Q E H+2).sum+3+
      work Q w h rs (updated Q E w h R) := rfl
#eval do
  let edge : Fin 1 × Fin 1 := (0,0)
  let zero : Sym2 (Fin 1) → ℚ := fun _ => 0
  let negative : Sym2 (Fin 1) → ℚ := fun _ => -3/2
  let noDraw : LightEFTSpanners.StoredHosts.TypedInput 1 := ⟨[],[]⟩
  let oneDraw : LightEFTSpanners.StoredHosts.TypedInput 1 := ⟨[],[[]]⟩
  let twoDraw : LightEFTSpanners.StoredHosts.TypedInput 1 := ⟨[],[[],[]]⟩
  let rich : LightEFTSpanners.StoredHosts.TypedInput 1 := ⟨[edge,edge,edge],[[edge,edge]]⟩
  let mk := fun (budget : ℚ) (hs : List (LightEFTSpanners.StoredHosts.TypedInput 1)) =>
    ({edge := edge, budget := budget, hosts := hs} : TypedInput 1)
  let bare := mk 0 []
  let one := mk 0 [oneDraw]
  let neg := mk (-1) [oneDraw]
  let checks := [
    decide (work (n:=0) [] (fun _ => 0) 0 [] [] = 1),
    decide (work [] zero 0 [] [edge,edge] = 1),
    decide (work [] zero 0 [bare] [] = 4),
    decide (work [] negative 999 [bare,bare] [edge] = 7),
    decide (work [] zero 0 (List.replicate 16 bare) [] = 49),
    decide (work [] zero 0 [mk 0 [noDraw]] [] = 10),
    decide (work [] zero 0 [one] [] = 55),
    decide (work [] zero 0 [one,one] [] = 110),
    decide (work [] zero 2 [one,one] [] = 109),
    decide (work [] zero 1 [one,one] [] = 109),
    decide (work [] zero 1 [neg,neg] [] = 110),
    decide (work [] negative 0 [one,one,one] [] = 166),
    decide (work [] zero 0 [one,one] [edge,edge] = 114),
    decide (work [edge,edge] zero 0 [one,one] [] = 114),
    decide (work [] zero 0 [mk 0 [twoDraw]] [] = 100),
    decide (work [] zero 0 [mk 0 [twoDraw],mk 0 [twoDraw]] [] = 201),
    decide (work [] zero 2 [mk 0 [twoDraw],mk 0 [twoDraw]] [] = 199),
    decide (work [] zero 0 [mk 0 [rich]] [] = 60),
    decide (work [] zero 0 [mk 0 [noDraw,oneDraw]] [] = 61),
    decide (work [] zero 0 [bare,one] [] = 59),
    decide (work [] zero 1 [bare,one] [] = 58),
    decide (work [] zero 0 [one,bare,one] [] = 114),
    decide (work [] zero 2 [one,bare,one] [] = 112),
    decide (work [] zero 0 (List.replicate 16 one) [] = 985)]
  unless checks.all id do throw (IO.userError "Exact state-dependent candidate work-count fixtures failed")
  unless updated [] [] zero 0 bare == [edge] do throw (IO.userError "threshold-zero update failed")
  unless updated [] [] zero 1 bare == [] do throw (IO.userError "empty-host rejection failed")
  unless updated [] [] zero 1 neg == [edge] do throw (IO.userError "negative-budget vote update failed")
  unless updated [] [edge] zero 1 one == [edge] do throw (IO.userError "nonnegative-budget rejection failed")
  IO.println s!"PASS: {checks.length} complete state-dependent candidate work-count fixtures; zero vertices, arbitrary weights/budgets, empty/duplicate hosts and edges, both update decisions, accumulated E charges and long lists"
  IO.println "PASS: four explicit updated-state fixtures"
