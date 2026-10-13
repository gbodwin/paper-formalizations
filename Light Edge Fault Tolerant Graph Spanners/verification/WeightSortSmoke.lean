import LightEFTSpanners.StoredWeightSortEncoding
open LightEFTSpanners

def check (name : String) (bank : StoredOriginalWeightLookup.Bank) (xs expected : List StoredEdges.Edge) : IO Unit := do
  let out := Controller.run (StoredWeightSort.transition bank) (StoredWeightSort.bound bank xs+1) (.sort xs [])
  match out with
  | .halt ys => unless ys==expected do throw (IO.userError ("FAIL sort "++name++" "++reprStr ys))
  | _ => throw (IO.userError ("FAIL sort not halted "++name))
  IO.println ("PASS sort "++name)

def main : IO Unit := do
  check "empty" [] [] []
  check "singleton" [] [(0,1)] [(0,1)]
  check "already-descending" [((0,1),3),((1,2),2)] [(0,1),(1,2)] [(0,1),(1,2)]
  check "ascending" [((0,1),1),((1,2),2)] [(0,1),(1,2)] [(1,2),(0,1)]
  check "stable-tie" [] [(0,1),(1,2)] [(0,1),(1,2)]
  check "odd-three" [((0,1),1),((1,2),3),((2,3),2)] [(0,1),(1,2),(2,3)] [(1,2),(2,3),(0,1)]
  check "even-four" [((0,1),1),((1,2),4),((2,3),2),((3,4),3)] [(0,1),(1,2),(2,3),(3,4)] [(1,2),(3,4),(2,3),(0,1)]
  check "stable-interleaved-ties" [((0,1),2),((1,2),1),((2,3),2),((3,4),1)] [(0,1),(1,2),(2,3),(3,4)] [(0,1),(2,3),(1,2),(3,4)]
  check "reverse-orientations" [((1,0),1),((2,1),2)] [(0,1),(1,2)] [(1,2),(0,1)]
  check "first-duplicate" [((0,1),1),((1,0),5),((1,2),2)] [(0,1),(1,2)] [(1,2),(0,1)]
  check "negative-missing" [((0,1),-1)] [(0,1),(1,2)] [(1,2),(0,1)]
  check "rational" [((0,1),(1:ℚ)/3),((1,2),(1:ℚ)/2)] [(0,1),(1,2)] [(1,2),(0,1)]
  check "duplicate-occurrences" [((0,1),1),((1,2),2)] [(0,1),(1,2),(0,1)] [(1,2),(0,1),(0,1)]
  check "five-all-ties" [] [(0,1),(1,2),(2,3),(3,4),(4,5)] [(0,1),(1,2),(2,3),(3,4),(4,5)]
