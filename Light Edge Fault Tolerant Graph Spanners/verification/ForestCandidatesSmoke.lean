import LightEFTSpanners.StoredForestCandidatesExecutable
open LightEFTSpanners

def input (e : StoredEdges.Edge) (bank : StoredDrawLookup.Bank) : StoredForestBank.Input := ⟨e,bank⟩
def check (name : String) (n h : ℕ) (fs : List (List StoredEdges.Edge))
    (Q E : List StoredEdges.Edge) (W : StoredRecords.Weights) (t : ℚ)
    (rs : List StoredForestBank.Input) (expected : List StoredEdges.Edge) : IO Unit := do
  let out := Controller.run (StoredForestCandidates.transition fs Q E W n h t)
    (StoredForestCandidates.bound n fs Q E rs) (.prepare (.inputs rs []))
  unless out==.select (.halt expected) do throw (IO.userError ("FAILED forest candidates "++name++" "++reprStr out))
  IO.println ("PASS forest candidates "++name)

def main : IO Unit := do
  let W : StoredRecords.Weights := [[0,5],[5,0]]
  check "empty-retains-seed" 2 1 [[(0,1)]] [(1,0)] [(1,0)] W 1 [] [(1,0)]
  check "zero-host-threshold" 2 0 [] [] [] W 1 [input (0,1) []] [(0,1)]
  check "positive-no-forest" 2 1 [] [] [] W 1 [input (0,1) []] []
  check "isolates-no-eligible-host" 2 1 [[]] [] [] W 1 [input (0,1) []] []
  check "missing-key-zero-vote" 2 1 [[(0,1)]] [] [] W 1 [input (0,1) []] []
  check "host-edge-rejects" 2 1 [[(0,1)]] [] [] W 1 [input (0,1) [(0,[[]])]] []
  check "zero-budget-admits" 2 1 [[(0,1)]] [] [] W 0 [input (0,1) [(0,[[]])]] [(0,1)]
  check "two-zero-threshold-order" 2 0 [[(0,1)]] [] [] W 1 [input (0,1) [],input (1,0) []] [(1,0),(0,1)]
  check "duplicate-zero-budget" 2 1 [[(0,1)]] [] [] W 0 [input (0,1) [(0,[[]])],input (0,1) [(0,[[]])]] [(0,1),(0,1)]
  check "host-threshold-two" 2 2 [[(0,1)],[(1,0)]] [] [] W 0 [input (0,1) [(0,[[]]),(2,[[]])]] [(0,1)]
