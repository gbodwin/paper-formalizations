import LightEFTSpanners.StoredVertexPairEncoding
open LightEFTSpanners

def check (name : String) (xs ys : List ℕ) (expected : List StoredEdges.Edge) : IO Unit := do
  let state := Controller.run StoredVertexPairs.transition (StoredVertexPairs.steps xs ys) (.rows xs ys [])
  unless state == .halt expected do throw (IO.userError ("FAILED vertex pairs "++name))
  IO.println ("PASS vertex pairs "++name)
def main : IO Unit := do
  check "both-empty" [] [] []
  check "left-empty" [] [0,1] []
  check "right-empty" [0,1] [] []
  check "singleton-diagonal" [2] [2] [(2,2)]
  check "stable-square" [1,0] [1,0] [(1,1),(1,0),(0,1),(0,0)]
  check "rectangular-repetitions" [2,2] [4,3] [(2,4),(2,3),(2,4),(2,3)]
