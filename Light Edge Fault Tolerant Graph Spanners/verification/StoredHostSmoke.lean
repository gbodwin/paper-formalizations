import LightEFTSpanners.StoredHostAdmission
open LightEFTSpanners

def require (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"

def main : IO Unit := do
  let W : StoredRecords.Weights := [[0,5],[5,0]]
  let yes : StoredHosts.Input := ⟨[],[[]]⟩
  let no : StoredHosts.Input := ⟨[(1,0)],[[]]⟩
  let empty : StoredHosts.Input := ⟨[],[]⟩
  let go := fun Q E h rs => StoredHosts.execute Q E W 2 0 1 h 5 rs
  require "no eligible hosts threshold zero" (go [] [] 0 [])
  require "no eligible hosts threshold one" (!go [] [] 1 [])
  require "one actual accepting host" (go [] [] 1 [yes])
  require "one actual rejecting host" (!go [] [] 1 [no])
  require "empty draw host rejects" (!go [] [] 1 [empty])
  require "mixed actual hosts threshold one" (go [] [] 1 [no,yes,no])
  require "mixed actual hosts threshold two" (!go [] [] 2 [no,yes,no])
  require "two accepting records threshold two" (go [] [] 2 [yes,no,yes])
  require "host edges override seed" (!go [(0,1)] [] 1 [no])
  require "seed clipping preserves accepting vote" (go [(1,0)] [(0,1)] 1 [⟨[],[[(0,1)]]⟩])
  require "duplicate reversed selected edges reject" (!go [] [(1,0),(0,1)] 1 [⟨[],[[(0,1),(1,0)]]⟩])
