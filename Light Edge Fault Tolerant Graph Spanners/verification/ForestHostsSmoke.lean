import LightEFTSpanners.StoredForestHostsExecutable
open LightEFTSpanners

def check (name : String) (n : ℕ) (fs : List (List StoredEdges.Edge))
    (expected : List StoredForestHosts.Record) : IO Unit := do
  let out := Controller.run (StoredForestHosts.transition n) (StoredForestHosts.bound n fs) (.forests 0 fs [])
  unless out==.halt expected do throw (IO.userError ("FAILED forest hosts "++name++" "++reprStr out))
  IO.println ("PASS forest hosts "++name)

def main : IO Unit := do
  check "empty-family" 3 [] []
  check "empty-vertex-set" 0 [[],[]] []
  check "single-isolate" 1 [[]] [(0,((0,[0]),[]))]
  check "two-isolate-forests" 1 [[],[]] [(0,((0,[0]),[])),(1,((0,[0]),[]))]
  check "one-edge" 2 [[(0,1)]] [(0,((0,[0,1]),[(0,1)]))]
  check "empty-then-edge" 2 [[],[(0,1)]] [(0,((0,[0]),[])),(0,((1,[1]),[])),(1,((0,[0,1]),[(0,1)]))]
  check "edge-then-empty" 2 [[(1,0)],[]] [(0,((0,[0,1]),[(1,0)])),(1,((0,[0]),[])),(1,((1,[1]),[]))]
  check "duplicate-forests" 2 [[(0,1)],[(0,1)]] [(0,((0,[0,1]),[(0,1)])),(1,((0,[0,1]),[(0,1)]))]
  check "loops-stripped" 2 [[(0,0),(1,1)],[(0,1),(1,1)]] [(0,((0,[0]),[])),(0,((1,[1]),[])),(1,((0,[0,1]),[(0,1)]))]
  check "two-partitions" 3 [[(0,1)],[(1,2)]] [(0,((0,[0,1]),[(0,1)])),(0,((2,[2]),[])),(1,((0,[0]),[])),(1,((1,[1,2]),[(1,2)]))]
