import LightEFTSpanners.StoredDrawLookupEncoding
open LightEFTSpanners StoredForestInput
-- Test-only equality compares every field recursively.
deriving instance DecidableEq for StoredHosts.TypedInput
deriving instance DecidableEq for StoredComponentRecord.TypedInput
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredForestInput.typedInputs
  let some c := env.find? name | throwError "typedInputs missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "typedInputs not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: typedInputs safe, total, computable, explicit List.rec, no partial companion"
example {n : ℕ} (bank : StoredDrawLookup.TypedBank n) (i : ℕ) : typedInputs bank i [] = [] := rfl
example {n : ℕ} (bank : StoredDrawLookup.TypedBank n) (i : ℕ)
    (es : List (Fin n × Fin n)) (rest : List (List (Fin n × Fin n))) :
    typedInputs bank i (es::rest) = (StoredCanonicalComponents.roots es).map (fun root =>
      ⟨StoredForestHosts.label n i root.val,StoredEdgeComponent.vertices es root,
        ⟨StoredDiscoveredHosts.typedHost es root,
          StoredDrawLookup.typedValue (StoredForestHosts.label n i root.val) bank⟩⟩) ++ typedInputs bank (i+1) rest := rfl
private def record (n id : ℕ) (vs : List (Fin n)) (es : List (Fin n × Fin n))
    (ds : List (List (Fin n × Fin n))) : StoredComponentRecord.TypedInput n := ⟨id,vs,⟨es,ds⟩⟩
private def a : List (List (Fin 3 × Fin 3)) := [[],[(2,1),(1,2),(2,2)],[(0,1),(0,1)]]
private def b : List (List (Fin 3 × Fin 3)) := [[(1,1)]]
private def huge : ℕ := 100000000000000000000
private def bank : StoredDrawLookup.TypedBank 3 :=
  [(0,a),(0,b),(1,[]),(2,b),(3,b),(6,a),(7,b),(huge*3,a),(huge*3+1,b),(huge*3+2,[])]
#eval do
  let checks : List Bool := [
    decide (typedInputs bank 0 [] = []),
    decide (typedInputs (n:=0) [(5,[[],[]])] huge [[],[],[]] = []),
    decide (typedInputs (n:=1) [] 0 [[]] = [record 1 0 [0] [] []]),
    decide (typedInputs (n:=1) [(4,[[(0,0)]]),(5,[])] 4 [[],[(0,0)]] =
      [record 1 4 [0] [] [[(0,0)]],record 1 5 [0] [] []]),
    decide (typedInputs (n:=3) [] 0 [[]] = [record 3 0 [0] [] [],record 3 1 [1] [] [],record 3 2 [2] [] []]),
    decide (typedInputs bank 0 [[]] = [record 3 0 [0] [] a,record 3 1 [1] [] [],record 3 2 [2] [] b]),
    decide (typedInputs (n:=3) [] 0 [[(1,2)]] = [record 3 0 [0] [] [],record 3 1 [1,2] [(1,2)] []]),
    decide (typedInputs bank 0 [[(2,1),(1,2),(2,1),(2,2)]] =
      [record 3 0 [0] [] a,record 3 1 [1,2] [(2,1),(1,2),(2,1)] []]),
    decide (typedInputs bank 0 [[(0,1),(1,2),(2,0)]] = [record 3 0 [0,1,2] [(0,1),(1,2),(2,0)] a]),
    decide (typedInputs bank 0 [[],[(0,1),(1,2)]] =
      [record 3 0 [0] [] a,record 3 1 [1] [] [],record 3 2 [2] [] b,record 3 3 [0,1,2] [(0,1),(1,2)] b]),
    decide (typedInputs bank 2 [[(1,2)],[]] =
      [record 3 6 [0] [] a,record 3 7 [1,2] [(1,2)] b,record 3 9 [0] [] [],record 3 10 [1] [] [],record 3 11 [2] [] []]),
    decide (typedInputs bank huge [[]] =
      [record 3 (huge*3) [0] [] a,record 3 (huge*3+1) [1] [] b,record 3 (huge*3+2) [2] [] []]),
    decide (typedInputs [(0,[]),(0,a)] 0 [[(0,1)]] = [record 3 0 [0,1] [(0,1)] [],record 3 2 [2] [] []]),
    decide (typedInputs [(0,b),(0,a)] 0 [[(0,1),(1,2),(2,0)]] = [record 3 0 [0,1,2] [(0,1),(1,2),(2,0)] b]),
    decide (typedInputs bank 1 [[(0,2)],[(0,2)]] =
      [record 3 3 [0,2] [(0,2)] b,record 3 4 [1] [] [],record 3 6 [0,2] [(0,2)] a,record 3 7 [1] [] b]),
    decide (typedInputs bank 0 [[(1,1),(0,0)]] = [record 3 0 [0] [] a,record 3 1 [1] [] [],record 3 2 [2] [] b]),
    decide (typedInputs bank 0 [[(1,2)],[(0,1)]] =
      [record 3 0 [0] [] a,record 3 1 [1,2] [(1,2)] [],record 3 3 [0,1] [(0,1)] b,record 3 5 [2] [] []])]
  unless checks.all id do throw (IO.userError "Complete typedInputs record fixtures failed")
  IO.println s!"PASS: {checks.length} full-record fixtures: every record field, arbitrary starting index, per-draw increment, root/concatenation order, zero/singleton vertices, isolated components, cycles, loops, duplicates/reversals and payload priority"
