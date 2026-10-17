import LightEFTSpanners.StoredCandidateTrace
open LightEFTSpanners.StoredCandidates
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredCandidates.selected
  let some c := env.find? name | throwError "selected missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "selected not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: selected safe, total, computable, explicit List.rec, no partial companion"
example {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (h : ℕ) :
    selected Q w h [] E = E := rfl
example {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (h : ℕ)
    (R : TypedInput n) (rs : List (TypedInput n)) :
    selected Q w h (R::rs) E = selected Q w h rs (updated Q E w h R) := rfl
#eval do
  let a : Fin 2 × Fin 2 := (0,1)
  let b : Fin 2 × Fin 2 := (1,0)
  let c : Fin 2 × Fin 2 := (0,0)
  let d : Fin 2 × Fin 2 := (1,1)
  let weight : Sym2 (Fin 2) → ℚ := fun _ => 1
  let negative : Sym2 (Fin 2) → ℚ := fun _ => -3/2
  let host : LightEFTSpanners.StoredHosts.TypedInput 2 := ⟨[],[[a]]⟩
  let blank : LightEFTSpanners.StoredHosts.TypedInput 2 := ⟨[],[[]]⟩
  let noDraw : LightEFTSpanners.StoredHosts.TypedInput 2 := ⟨[],[]⟩
  let mk := fun (edge : Fin 2 × Fin 2) (budget : ℚ) (hs : List (LightEFTSpanners.StoredHosts.TypedInput 2)) =>
    ({edge := edge,budget := budget,hosts := hs} : TypedInput 2)
  let bare := fun edge => mk edge 0 []
  let sampled := fun edge => mk edge 1 [host]
  let checks := [
    decide (selected (n:=0) [] (fun _ => 0) 0 [] [] = []),
    decide (selected [] weight 0 [] [b,a,b] = [b,a,b]),
    decide (selected [] weight 0 [bare a] [b] = [a,b]),
    decide (selected [] weight 0 [bare a,bare b,bare c] [b,a] = [c,b,a,b,a]),
    decide (selected [] weight 0 [bare a,bare a,bare b] [a,a] = [b,a,a,a,a]),
    decide (selected [] negative 0 [bare d,bare c] [b] = [c,d,b]),
    decide (selected [] weight 9 [bare a,bare b] [b,a,b] = [b,a,b]),
    decide (selected [] weight 1 [mk a 0 [noDraw]] [b] = [b]),
    decide (selected [] weight 1 [sampled a] [] = [a]),
    decide (selected [] weight 1 [sampled a,sampled a] [] = [a]),
    decide (selected [] weight 1 [sampled a,sampled b] [] = [a]),
    decide (selected [a] weight 1 [sampled a,sampled a] [] = [a,a]),
    decide (selected [a,a] weight 1 [sampled a,sampled b] [] = [b,a]),
    decide (selected [] weight 1 [sampled a] [a,a] = [a,a]),
    decide (selected [] weight 1 [sampled a] [b] = [b]),
    decide (selected [] weight 1 [mk a 1 [blank],mk a 1 [blank]] [] = [a,a]),
    decide (selected [] weight 1 [mk a 0 [host],mk a 0 [host]] [] = [a,a]),
    decide (selected [] weight 1 [mk c (-1) [host],mk d (-1) [host]] [] = [d,c]),
    decide (selected [] weight 1 [sampled a,mk c (-1) [host],sampled b] [] = [c,a]),
    decide (selected [] weight 2 [sampled a,sampled b] [c] = [c]),
    decide (selected [] weight 0 (List.replicate 16 (bare a)) [b] = List.replicate 16 a ++ [b]),
    decide (selected [] weight 1 (List.replicate 16 (sampled a)) [] = [a]),
    decide (selected [a] weight 1 (List.replicate 16 (sampled a)) [] = List.replicate 16 a),
    decide (selected [] weight 1 [mk a 1 [host,host],mk b 1 [host,host]] [c,c] = [a,c,c])]
  unless checks.all id do throw (IO.userError "Exact candidate final-list fixtures failed")
  unless updated [] [] weight 1 (sampled a) == [a] do throw (IO.userError "initial acceptance failed")
  unless updated [] [a] weight 1 (sampled a) == [a] do throw (IO.userError "updated-state rejection failed")
  unless updated [a] [a] weight 1 (sampled a) == [a,a] do throw (IO.userError "Q exclusion duplicate acceptance failed")
  unless updated [] [b,a] weight 0 (bare c) == [c,b,a] do throw (IO.userError "ordered prepend failed")
  IO.println s!"PASS: {checks.length} complete candidate final-list fixtures; arbitrary initial E, exact order and duplicates, negative weights/budgets, accept/reject accumulation, state-dependent rejection, Q exclusion and long lists"
  IO.println "PASS: four explicit updated-state fixtures"
