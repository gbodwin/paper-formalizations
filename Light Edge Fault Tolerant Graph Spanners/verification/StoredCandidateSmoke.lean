import LightEFTSpanners.StoredCandidateExecutable
open LightEFTSpanners

def require (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"

def main : IO Unit := do
  let W : StoredRecords.Weights := [[0,5],[5,0]]
  let yes : StoredHosts.Input := ⟨[],[[]]⟩
  let no : StoredHosts.Input := ⟨[(0,1)],[[]]⟩
  let sampled : StoredHosts.Input := ⟨[],[[(1,0)]]⟩
  let a : StoredCandidates.Input := ⟨(0,1),5,[yes]⟩
  let b : StoredCandidates.Input := ⟨(1,0),5,[sampled]⟩
  let go := fun Q h rs => StoredCandidates.execute Q Q W 2 h rs
  require "empty order retains exact seed" (go [(1,0)] 1 []==[(1,0)])
  require "accepted edge is stored" (go [] 1 [a]==[(0,1)])
  require "second candidate reads actual updated edge" (go [] 1 [a,b]==[(0,1)])
  require "reversing execution order changes stored orientation" (go [] 1 [b,a]==[(0,1),(1,0)])
  require "rejected candidate preserves seed" (go [(1,0)] 1 [⟨(0,1),5,[no]⟩]==[(1,0)])
  require "zero threshold admits without hosts" (go [] 0 [⟨(1,0),5,[]⟩]==[(1,0)])
  require "positive threshold rejects without hosts" (go [] 1 [⟨(1,0),5,[]⟩]==[])
  require "duplicate accepted candidate cells remain charged" (go [] 1 [a,a]==[(0,1),(0,1)])
