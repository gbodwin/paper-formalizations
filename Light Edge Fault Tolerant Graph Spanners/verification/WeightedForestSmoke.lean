import LightEFTSpanners.StoredWeightedForestExecution
open LightEFTSpanners

def input (e : StoredEdges.Edge) (draws : StoredDrawLookup.Bank) : StoredForestBank.Input := ⟨e,draws⟩
def check (name : String) (n h : ℕ) (fs : List (List StoredEdges.Edge)) (Q E : List StoredEdges.Edge)
    (bank : StoredOriginalWeightLookup.Bank) (t : ℚ) (rs : List StoredForestBank.Input)
    (expected : List StoredEdges.Edge) : IO Unit := do
  let out := Controller.run (StoredWeightedForestCandidates.transition n h fs Q E bank t rs)
    (StoredWeightedForestCandidates.bound n fs Q E bank rs) (.weights (.rows 0 n []))
  match out with
  | .candidates _ (.select (.halt es)) => unless es==expected do throw (IO.userError ("FAIL weighted forest "++name++" "++reprStr out))
  | _ => throw (IO.userError ("FAIL weighted forest not halted "++name))
  IO.println ("PASS weighted forest "++name)

def main : IO Unit := do
  check "empty-retains-seed" 2 1 [[(0,1)]] [(1,0)] [(1,0)] [((0,1),5)] 1 [] [(1,0)]
  check "actual-positive-weight-rejects" 2 1 [[(0,1)]] [] [] [((0,1),5)] 1 [input (0,1) [(0,[[]])]] []
  check "actual-zero-budget-admits" 2 1 [[(0,1)]] [] [] [((0,1),5)] 0 [input (0,1) [(0,[[]])]] [(0,1)]
  check "duplicate-first-match-rejects" 2 1 [[(0,1)]] [] [] [((0,1),5),((1,0),0)] 1 [input (0,1) [(0,[[]])]] []
  check "zero-host-threshold" 2 0 [] [] [] [] 1 [input (0,1) [],input (1,0) []] [(1,0),(0,1)]
  check "two-hosts" 2 2 [[(0,1)],[(1,0)]] [] [] [((1,0),3)] 0 [input (0,1) [(0,[[]]),(2,[[]])]] [(0,1)]
