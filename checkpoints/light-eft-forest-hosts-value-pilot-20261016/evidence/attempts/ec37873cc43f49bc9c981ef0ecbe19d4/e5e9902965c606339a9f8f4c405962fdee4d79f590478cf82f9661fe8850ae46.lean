import LightEFTSpanners.StoredForestHosts
open LightEFTSpanners.StoredForestHosts
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredForestHosts.value
  let some c := env.find? name | throwError "value missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "value not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: value safe, total, computable, explicit List.rec, no partial companion"
example {n : ℕ} (i : ℕ) : value (n:=n) i [] = [] := rfl
example {n : ℕ} (i : ℕ) (es : List (Fin n × Fin n)) (fs : List (List (Fin n × Fin n))) :
    value i (es::fs) = (LightEFTSpanners.StoredDiscoveredHosts.value es).map (fun r => (i,r)) ++ value (i+1) fs := rfl
private def r (i root : ℕ) (vs : List ℕ) (es : List (ℕ × ℕ)) : Record := (i,((root,vs),es))
#eval do
  let checks := [
    decide (value (n:=0) 0 [] = []),
    decide (value (n:=0) 100000000000000000000 [[],[],[]] = []),
    decide (value (n:=1) 99 [] = []),
    decide (value (n:=1) 0 [[]] = [r 0 0 [0] []]),
    decide (value (n:=1) 7 [[],[]] = [r 7 0 [0] [],r 8 0 [0] []]),
    decide (value (n:=2) 3 [[]] = [r 3 0 [0] [],r 3 1 [1] []]),
    decide (value (n:=2) 0 [[(0,1)]] = [r 0 0 [0,1] [(0,1)]]),
    decide (value (n:=2) 5 [[(1,0)]] = [r 5 0 [0,1] [(1,0)]]),
    decide (value (n:=2) 2 [[(0,1),(1,0),(0,1)]] = [r 2 0 [0,1] [(0,1),(1,0),(0,1)]]),
    decide (value (n:=2) 4 [[(0,0),(1,1)]] = [r 4 0 [0] [],r 4 1 [1] []]),
    decide (value (n:=3) 1 [[(0,1),(1,2),(2,0)]] = [r 1 0 [0,1,2] [(0,1),(1,2),(2,0)]]),
    decide (value (n:=4) 9 [[(0,1),(2,3)]] = [r 9 0 [0,1] [(0,1)],r 9 2 [2,3] [(2,3)]]),
    decide (value (n:=2) 8 [[],[(0,1)]] = [r 8 0 [0] [],r 8 1 [1] [],r 9 0 [0,1] [(0,1)]]),
    decide (value (n:=2) 8 [[(0,1)],[]] = [r 8 0 [0,1] [(0,1)],r 9 0 [0] [],r 9 1 [1] []]),
    decide (value (n:=2) 4 [[(0,1)],[(0,1)]] = [r 4 0 [0,1] [(0,1)],r 5 0 [0,1] [(0,1)]]),
    decide (value (n:=3) 6 [[(1,2)]] = [r 6 0 [0] [],r 6 1 [1,2] [(1,2)]]),
    decide (value (n:=1) 100000000000000000000 [[],[]] = [r 100000000000000000000 0 [0] [],r 100000000000000000001 0 [0] []]),
    decide (value (n:=1) 2 [[],[],[]] = [r 2 0 [0] [],r 3 0 [0] [],r 4 0 [0] []]),
    decide (value (n:=3) 10 [[]] = [r 10 0 [0] [],r 10 1 [1] [],r 10 2 [2] []]),
    decide (value (n:=2) 3 [[(0,0),(1,0),(1,1),(0,1)]] = [r 3 0 [0,1] [(1,0),(0,1)]])]
  unless checks.all id do throw (IO.userError "Complete ordered forest host record fixtures failed")
  IO.println s!"PASS: {checks.length} complete record-list fixtures; n=0, empty inputs, arbitrary start, incrementing forest indices, isolated/connected components, record and edge order, repeated forests, loops, duplicate edges, cycles and huge indices"
