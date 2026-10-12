import LightEFTSpanners.StoredForestInputEncoding
open LightEFTSpanners

def record (id : ℕ) (vs : List ℕ) (es : List StoredEdges.Edge) (ds : StoredVote.Draws) : StoredComponentRecord.Input :=
  ⟨id,vs,⟨es,ds⟩⟩

def check (name : String) (n : ℕ) (fs : List (List StoredEdges.Edge)) (bank : StoredDrawLookup.Bank)
    (expected : List StoredComponentRecord.Input) : IO Unit := do
  let out := Controller.run (StoredForestInput.transition n bank) (StoredForestInput.bound n fs bank)
    (.forests (.forests 0 fs []))
  unless out==.halt expected do throw (IO.userError ("FAILED forest input "++name++" "++reprStr out))
  IO.println ("PASS forest input "++name)

def main : IO Unit := do
  check "no-forests" 3 [] [] []
  check "empty-order" 0 [[],[]] [(0,[[]])] []
  check "missing-key" 1 [[]] [] [record 0 [0] [] []]
  check "single-draw" 1 [[]] [(0,[[]])] [record 0 [0] [] [[]]]
  check "first-match" 1 [[]] [(0,[[],[]]),(0,[])] [record 0 [0] [] [[],[]]]
  check "late-match" 1 [[]] [(3,[]),(0,[[]])] [record 0 [0] [] [[]]]
  check "edge-host" 2 [[(0,1)]] [(0,[[(0,1)]])] [record 0 [0,1] [(0,1)] [[(0,1)]]]
  check "isolate-labels" 2 [[]] [(1,[[]]),(0,[])] [record 0 [0] [] [],record 1 [1] [] [[]]]
  check "two-forest-labels" 2 [[(0,1)],[(1,0)]] [(2,[[(1,0)]]),(0,[[]])] [record 0 [0,1] [(0,1)] [[]],record 2 [0,1] [(1,0)] [[(1,0)]]]
  check "loop-and-duplicates" 2 [[(0,0),(0,1),(0,1)]] [(0,[[(0,1)],[(1,0)]])] [record 0 [0,1] [(0,1),(0,1)] [[(0,1)],[(1,0)]]]
  check "unused-bank-keys" 1 [[]] [(10,[[(8,9)]]),(0,[[]]),(20,[])] [record 0 [0] [] [[]]]
  check "two-partitions" 3 [[(0,1)],[(1,2)]] [(0,[[]]),(2,[]),(3,[[],[]]),(4,[[(1,2)]])] [record 0 [0,1] [(0,1)] [[]],record 2 [2] [] [],record 3 [0] [] [[],[]],record 4 [1,2] [(1,2)] [[(1,2)]]]
