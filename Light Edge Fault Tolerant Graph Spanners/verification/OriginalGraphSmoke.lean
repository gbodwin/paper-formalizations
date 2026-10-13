import LightEFTSpanners.StoredOriginalGraphExecutable
open LightEFTSpanners

def check (name : String) (n h : ℕ) (fs : List (List StoredEdges.Edge)) (Q E xs : List StoredEdges.Edge)
    (weights : StoredOriginalWeightLookup.Bank) (bank : StoredCandidateDrawLookup.Bank) (t : ℚ)
    (expected : List StoredEdges.Edge) : IO Unit := do
  let out := Controller.run (StoredOriginalGraphCaller.transition n h fs Q E weights bank t)
    (StoredOriginalGraphCaller.bound n fs Q E xs weights bank) (.prepare (.sorting (.sort xs [])))
  match out with
  | .run _ (.candidates _ (.select (.halt es))) =>
    unless es==expected do throw (IO.userError ("FAIL original graph "++name++" "++reprStr es))
  | _ => throw (IO.userError ("FAIL original graph not halted "++name))
  IO.println ("PASS original graph "++name)

def main : IO Unit := do
  check "empty" 0 1 [] [] [] [] [] [] 1 []
  check "retained-seed" 2 1 [[(0,1)]] [(1,0)] [(1,0)] [] [((0,1),5)] [] 1 [(1,0)]
  check "seed-filter" 2 0 [] [(1,0)] [(1,0)] [(0,1)] [] [] 0 [(1,0)]
  check "positive-budget-rejects" 2 1 [[(0,1)]] [] [] [(0,1)] [((0,1),5)] [((0,1),[(0,[[]])])] 1 []
  check "zero-budget-admits" 2 1 [[(0,1)]] [] [] [(0,1)] [((0,1),5)] [((0,1),[(0,[[]])])] 0 [(0,1)]
  check "reversed-draw-key" 2 1 [[(0,1)]] [] [] [(0,1)] [((0,1),5)] [((1,0),[(0,[[]])])] 0 [(0,1)]
  check "first-draw-match" 2 1 [[(0,1)]] [] [] [(0,1)] [] [((0,1),[]),((1,0),[(0,[[]])])] 0 []
  check "missing-draw" 2 1 [[(0,1)]] [] [] [(0,1)] [] [] 0 []
  check "stable-ties" 3 0 [] [] [] [(0,1),(1,2)] [] [] 0 [(0,1),(1,2)]
  check "actual-descending-order" 3 0 [] [] [] [(0,1),(1,2)] [((0,1),1),((1,2),2)] [] 0 [(1,2),(0,1)]
  check "duplicate-occurrences" 2 0 [] [] [] [(0,1),(1,0),(0,1)] [] [] 0 [(0,1),(1,0),(0,1)]
  check "two-hosts" 2 2 [[(0,1)],[(1,0)]] [] [] [(0,1)] [((1,0),3)] [((0,1),[(0,[[]]),(2,[[]])])] 0 [(0,1)]
