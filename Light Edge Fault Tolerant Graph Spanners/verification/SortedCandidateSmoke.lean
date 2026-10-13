import LightEFTSpanners.StoredSortedCandidateExecutable
open LightEFTSpanners

def record (x : StoredEdges.Edge) (bank : StoredDrawLookup.Bank := []) : StoredForestBank.Input := ⟨x,bank⟩
def check (name : String) (w : StoredOriginalWeightLookup.Bank) (Q : List StoredEdges.Edge)
    (draws : StoredCandidateDrawLookup.Bank) (xs : List StoredEdges.Edge) (expected : List StoredForestBank.Input) : IO Unit := do
  let out := Controller.run (StoredSortedCandidateInput.transition w Q draws) (StoredSortedCandidateInput.bound w Q draws xs)
    (.sorting (.sort xs []))
  match out with
  | .records (.halt rs) => unless rs==expected do throw (IO.userError ("FAIL input "++name++" "++reprStr rs))
  | _ => throw (IO.userError ("FAIL input not halted "++name))
  IO.println ("PASS input "++name)

def main : IO Unit := do
  check "empty" [] [] [] [] []
  check "singleton-missing-draw" [] [] [] [(0,1)] [record (0,1)]
  check "seed-excluded" [] [(0,1)] [] [(0,1)] []
  check "reversed-seed-excluded" [] [(1,0)] [] [(0,1)] []
  check "actual-weight-order" [((0,1),1),((1,2),2)] [] [] [(1,2),(0,1)] [record (0,1),record (1,2)]
  check "tie-reversal" [] [] [] [(0,1),(1,2)] [record (1,2),record (0,1)]
  check "draw-preserved" [] [] [((0,1),[(7,[[(1,2)]])])] [(0,1)] [record (0,1) [(7,[[(1,2)]])]]
  check "reversed-draw-key" [] [] [((1,0),[(7,[[(1,2)]])])] [(0,1)] [record (0,1) [(7,[[(1,2)]])]]
  check "first-duplicate-draw" [] [] [((0,1),[]),((1,0),[(7,[[]])])] [(0,1)] [record (0,1)]
  check "late-key" [] [] [((2,3),[]),((0,1),[(7,[[]])])] [(0,1)] [record (0,1) [(7,[[]])]]
  check "mixed-seed" [((0,1),3),((1,2),1),((2,3),2)] [(1,0)] [] [(1,2),(0,1),(2,3)] [record (1,2),record (2,3)]
  check "duplicates-retained" [] [] [] [(0,1),(1,0),(0,1)] [record (0,1),record (1,0),record (0,1)]
  check "negative-missing-weight" [((0,1),-1)] [] [] [(1,2),(0,1)] [record (0,1),record (1,2)]
  check "all-excluded" [] [(0,1),(2,1)] [] [(0,1),(1,2)] []
