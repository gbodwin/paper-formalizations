import LightEFTSpanners.StoredForestBankExecutable
open LightEFTSpanners

def host (es : List StoredEdges.Edge) (ds : StoredVote.Draws) : StoredHosts.Input := ⟨es,ds⟩
def output (e : StoredEdges.Edge) (budget : ℚ) (hs : List StoredHosts.Input) : StoredCandidates.Input := ⟨e,budget,hs⟩
def input (e : StoredEdges.Edge) (bank : StoredDrawLookup.Bank) : StoredForestBank.Input := ⟨e,bank⟩

def check (name : String) (n : ℕ) (fs : List (List StoredEdges.Edge))
    (W : StoredRecords.Weights) (t : ℚ) (rs : List StoredForestBank.Input)
    (expected : List StoredCandidates.Input) : IO Unit := do
  let out := Controller.run (StoredForestBank.transition n fs W t)
    (StoredForestBank.bound n fs rs) (.inputs rs [])
  unless out==.halt expected do throw (IO.userError ("FAILED forest bank "++name++" "++reprStr out))
  IO.println ("PASS forest bank "++name)

def main : IO Unit := do
  let W : StoredRecords.Weights := [[0,2],[2,0]]
  check "empty" 2 [[(0,1)]] W 3 [] []
  check "single" 2 [[(0,1)]] W 3 [input (0,1) [(0,[[]])]] [output (0,1) 6 [host [(0,1)] [[]]]]
  check "two-orders" 2 [[(0,1)]] W 2 [input (0,1) [(0,[[]])],input (1,0) [(0,[])]] [output (0,1) 4 [host [(0,1)] [[]]],output (1,0) 4 [host [(0,1)] []]]
  check "duplicate-candidate" 2 [[(0,1)]] W 1 [input (0,1) [(0,[[]])],input (0,1) [(0,[[],[]])]] [output (0,1) 2 [host [(0,1)] [[]]],output (0,1) 2 [host [(0,1)] [[],[]]]]
  check "no-forests" 2 [] W 3 [input (0,1) [],input (1,0) []] [output (0,1) 6 [],output (1,0) 6 []]
  check "isolates" 2 [[]] W 3 [input (0,1) [],input (0,0) [(0,[[]])]] [output (0,1) 6 [],output (0,0) 0 [host [] [[]]]]
  check "two-forest-bank" 2 [[(0,1)],[(1,0)]] W 1 [input (0,1) [(0,[[]]),(2,[])]] [output (0,1) 2 [host [(0,1)] [[]],host [(1,0)] []]]
  check "empty-weights" 2 [[(0,1)]] [] 3 [input (0,1) []] [output (0,1) 0 [host [(0,1)] []]]
  check "first-match-bank" 2 [[(0,1)]] W 3 [input (0,1) [(0,[[]]),(0,[])]] [output (0,1) 6 [host [(0,1)] [[]]]]
  check "zero-threshold" 2 [[(0,1)]] W 0 [input (0,1) []] [output (0,1) 0 [host [(0,1)] []]]
