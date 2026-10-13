import LightEFTSpanners.StoredWeightMergeBound
open LightEFTSpanners

def check (name : String) (bank : StoredOriginalWeightLookup.Bank)
    (xs ys expected : List StoredEdges.Edge) : IO Unit := do
  let state := Controller.run (StoredWeightMerge.transition bank) (StoredWeightMerge.bound bank xs ys) (.merge xs ys [])
  match state with
  | .halt out => unless out==expected do throw (IO.userError ("FAIL merge "++name++" "++reprStr out))
  | _ => throw (IO.userError ("FAIL merge not halted "++name))
  IO.println ("PASS merge "++name)

def main : IO Unit := do
  check "empty" [] [] [] []
  check "left-empty" [] [] [(0,1),(1,2)] [(0,1),(1,2)]
  check "right-empty" [] [(0,1),(1,2)] [] [(0,1),(1,2)]
  check "decreasing" [((0,1),3),((1,2),2)] [(0,1)] [(1,2)] [(0,1),(1,2)]
  check "right-first" [((0,1),1),((1,2),2)] [(0,1)] [(1,2)] [(1,2),(0,1)]
  check "stable-tie" [((0,1),2),((1,2),2)] [(0,1)] [(1,2)] [(0,1),(1,2)]
  check "reverse-orientation" [((1,0),3),((2,1),2)] [(0,1)] [(1,2)] [(0,1),(1,2)]
  check "first-duplicate" [((0,1),1),((1,0),5),((1,2),2)] [(0,1)] [(1,2)] [(1,2),(0,1)]
  check "missing-zero" [((1,2),-1)] [(0,1)] [(1,2)] [(0,1),(1,2)]
  check "interleaving" [((0,1),4),((1,2),3),((2,3),2),((3,4),1)] [(0,1),(2,3)] [(1,2),(3,4)] [(0,1),(1,2),(2,3),(3,4)]
  check "all-ties-stable" [] [(0,1),(2,3)] [(1,2),(3,4)] [(0,1),(2,3),(1,2),(3,4)]
  check "rational-negative" [((0,1),(-1:ℚ)/3),((1,2),(-1:ℚ)/2)] [(0,1)] [(1,2)] [(0,1),(1,2)]
