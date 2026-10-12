import LightEFTSpanners.StoredEdgeComponent
open LightEFTSpanners

def check (name : String) (n root : ℕ) (edges : List StoredEdges.Edge) (expected : List ℕ) : IO Unit := do
  let out := Controller.run (StoredEdgeComponent.transition n root edges)
    (StoredEdgeComponent.bound n edges.length) (.matrix (.zero (.row n [])))
  unless out==.halt expected do throw (IO.userError ("FAILED component discovery "++name++" "++reprStr out))
  IO.println ("PASS component discovery "++name)

def main : IO Unit := do
  check "empty" 0 0 [] []
  check "singleton" 1 0 [] [0]
  check "diagonal" 1 0 [(0,0)] [0]
  check "edge" 2 0 [(0,1)] [0,1]
  check "reversed" 2 1 [(1,0)] [0,1]
  check "duplicates" 2 1 [(0,1),(1,0),(0,1)] [0,1]
  check "chain" 4 0 [(0,1),(1,2),(2,3)] [0,1,2,3]
  check "reverse-chain" 4 3 [(2,3),(1,2),(0,1)] [0,1,2,3]
  check "disconnected" 5 0 [(0,2),(1,3)] [0,2]
  check "isolated" 5 4 [(0,2),(1,3)] [4]
  check "cycle" 4 2 [(0,1),(1,2),(2,0)] [0,1,2]
  check "star" 4 3 [(0,1),(0,2),(0,3)] [0,1,2,3]
  check "out-of-range-edge" 3 0 [(0,1),(1,8),(8,2)] [0,1]
  check "loops-and-components" 4 2 [(0,0),(1,1),(2,2),(3,3),(1,3)] [2]
