import LightEFTSpanners.StoredDiscoveredHostsCorrect
open LightEFTSpanners

def check (name : String) (n : ℕ) (edges : List StoredEdges.Edge)
    (expected : List StoredCanonicalHosts.Record) : IO Unit := do
  let out := Controller.run (StoredDiscoveredHosts.transition n edges)
    (StoredDiscoveredHosts.bound n edges.length) (.components (.range n []))
  unless out==.halt expected do throw (IO.userError ("FAILED discovered hosts "++name++" "++reprStr out))
  IO.println ("PASS discovered hosts "++name)

def main : IO Unit := do
  check "empty" 0 [] []
  check "singleton" 1 [] [((0,[0]),[])]
  check "isolated-pair" 2 [] [((0,[0]),[]),((1,[1]),[])]
  check "diagonal-only" 2 [(0,0),(1,1)] [((0,[0]),[]),((1,[1]),[])]
  check "edge" 2 [(0,1)] [((0,[0,1]),[(0,1)])]
  check "reversed-edge" 2 [(1,0)] [((0,[0,1]),[(1,0)])]
  check "duplicate-edges" 2 [(0,1),(1,0),(0,1)] [((0,[0,1]),[(0,1),(1,0),(0,1)])]
  check "chain" 4 [(0,1),(1,2),(2,3)] [((0,[0,1,2,3]),[(0,1),(1,2),(2,3)])]
  check "reversed-chain" 4 [(2,3),(1,2),(0,1)] [((0,[0,1,2,3]),[(2,3),(1,2),(0,1)])]
  check "disconnected" 4 [(0,2),(1,3)] [((0,[0,2]),[(0,2)]),((1,[1,3]),[(1,3)])]
  check "middle-isolate" 4 [(0,3),(3,2)] [((0,[0,2,3]),[(0,3),(3,2)]),((1,[1]),[])]
  check "cycle-and-isolate" 4 [(1,2),(2,3),(3,1)] [((0,[0]),[]),((1,[1,2,3]),[(1,2),(2,3),(3,1)])]
  check "star-with-loop" 4 [(3,0),(3,3),(3,1),(3,2)] [((0,[0,1,2,3]),[(3,0),(3,1),(3,2)])]
  check "outside-labels" 3 [(0,1),(1,8),(8,2)] [((0,[0,1]),[(0,1)]),((2,[2]),[])]
