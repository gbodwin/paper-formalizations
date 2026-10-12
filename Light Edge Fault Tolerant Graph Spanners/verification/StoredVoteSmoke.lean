import LightEFTSpanners.StoredVoteExecutable
open LightEFTSpanners

def require (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"

def main : IO Unit := do
  let W : StoredRecords.Weights := [[0,5],[5,0]]
  let go := fun Q E T ss => StoredVote.execute Q E T W 2 0 1 5 ss
  require "empty actual draw list" (!go [] [] [] [])
  require "unreachable actual draw" (go [] [] [] [[]])
  require "reversed actual selected edge" (!go [] [(0,1)] [] [[(1,0)]])
  require "actual seed clipping" (go [(1,0)] [(0,1)] [] [[(0,1)]])
  require "actual host overrides seed" (!go [(0,1)] [] [(1,0)] [[]])
  require "one of three failures below three eighths" (!go [] [(0,1)] [] [[(1,0)],[],[(0,1)]])
  require "one of two failures above three eighths" (go [] [(0,1)] [] [[(1,0)],[]])
  require "duplicate draw cells preserved" (!go [] [(1,0),(0,1)] [] [[(0,1),(1,0)]])
