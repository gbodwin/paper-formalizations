import LightEFTSpanners.StoredForestCandidateEncoding
open LightEFTSpanners

def host (es : List StoredEdges.Edge) (ds : StoredVote.Draws) : StoredHosts.Input := ⟨es,ds⟩
def output (e : StoredEdges.Edge) (budget : ℚ) (hs : List StoredHosts.Input) : StoredCandidates.Input := ⟨e,budget,hs⟩

def check (name : String) (n : ℕ) (fs : List (List StoredEdges.Edge)) (bank : StoredDrawLookup.Bank)
    (e : StoredEdges.Edge) (W : StoredRecords.Weights) (t : ℚ) (expected : StoredCandidates.Input) : IO Unit := do
  let out := Controller.run (StoredForestCandidate.transition n bank e W t)
    (StoredForestCandidate.bound n fs bank e) (.inputs (.forests (.forests 0 fs [])))
  unless out==.halt expected do throw (IO.userError ("FAILED forest candidate "++name++" "++reprStr out))
  IO.println ("PASS forest candidate "++name)

def main : IO Unit := do
  let W : StoredRecords.Weights := [[0,2],[2,0]]
  check "empty-family" 2 [] [] (0,1) W 3 (output (0,1) 6 [])
  check "isolates-ineligible" 2 [[]] [] (0,1) W 3 (output (0,1) 6 [])
  check "single-host" 2 [[(0,1)]] [(0,[[]])] (0,1) W 3 (output (0,1) 6 [host [(0,1)] [[]]])
  check "missing-draw-key" 2 [[(0,1)]] [] (0,1) W 3 (output (0,1) 6 [host [(0,1)] []])
  check "reversed-candidate" 2 [[(0,1)]] [(0,[[(0,1)]])] (1,0) W 2 (output (1,0) 4 [host [(0,1)] [[(0,1)]]])
  check "two-hosts" 2 [[(0,1)],[(1,0)]] [(0,[[]]),(2,[[(1,0)]])] (0,1) W 1 (output (0,1) 2 [host [(0,1)] [[]],host [(1,0)] [[(1,0)]]])
  check "first-key" 2 [[(0,1)]] [(0,[[]]),(0,[])] (0,1) W 0 (output (0,1) 0 [host [(0,1)] [[]]])
  check "diagonal-eligibility" 2 [[]] [(0,[[]])] (0,0) W 2 (output (0,0) 0 [host [] [[]]])
  check "host-loops-stripped" 2 [[(0,0),(0,1),(1,1)]] [(0,[[]])] (0,1) W 1 (output (0,1) 2 [host [(0,1)] [[]]])
  check "host-duplicates-kept" 2 [[(0,1),(0,1)]] [(0,[[]])] (0,1) W 1 (output (0,1) 2 [host [(0,1),(0,1)] [[]]])
  check "empty-matrix" 2 [[(0,1)]] [(0,[[]])] (0,1) [] 3 (output (0,1) 0 [host [(0,1)] [[]]])
  check "later-forest-only" 2 [[],[(0,1)]] [(2,[[]])] (0,1) W 3 (output (0,1) 6 [host [(0,1)] [[]]])
