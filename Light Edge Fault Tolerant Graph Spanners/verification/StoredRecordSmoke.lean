import LightEFTSpanners.StoredRecordEncoding

open LightEFTSpanners

def require (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"

def main : IO Unit := do
  let q : StoredEdges.Edge := (1,2)
  require "reversed edge" (Controller.run StoredEdges.transition 4 (.scan q [(5,6),(2,1),(7,8)]) == .halt true)
  require "missing edge" (Controller.run StoredEdges.transition 3 (.scan q [(1,3),(2,4)]) == .halt false)
  require "duplicate occurrence" (Controller.run StoredEdges.transition 4 (.scan q [(9,9),(1,2),(1,2)]) == .halt true)
  let es : StoredSample.EdgeLists := ⟨[(2,1)],[(1,2)],[],[(2,1)]⟩
  require "four actual scans" (Controller.run (StoredSample.transition q 7 es) 11
    (.seed (.scan q es.seed)) == .halt ⟨7,true,true,false,true⟩)
  let empty : StoredSample.EdgeLists := ⟨[],[],[],[]⟩
  require "empty raw matrix" (Controller.run (StoredRecords.transition empty) 2 (.row 0 [] []) == .halt [])
  let weights : StoredRecords.Weights := [[0,5],[5,0]]
  let cell : SampleRecords.Entry := ⟨0,false,false,false,false⟩
  require "literal two-by-two construction" (Controller.run (StoredRecords.transition empty) 54
    (.row 0 weights []) == .halt [[cell,⟨5,false,false,false,false⟩],[⟨5,false,false,false,false⟩,cell]])
  let masks : StoredSample.EdgeLists := ⟨[(0,1)],[(0,1),(1,0)],[],[(1,0)]⟩
  let constructed := Controller.run (StoredRecords.transition masks) 100 (.row 0 weights [])
  match constructed with
  | .halt R => require "seed clipping after constructed membership" (SampleRecords.values 0 R == [[none,none],[none,none]])
  | _ => throw (IO.userError "matrix construction did not halt")
  let hosted : StoredSample.EdgeLists := ⟨[(0,1)],[],[(1,0)],[]⟩
  match Controller.run (StoredRecords.transition hosted) 100 (.row 0 weights []) with
  | .halt R => require "host survives seed clipping" (SampleRecords.values 0 R == [[none,some 5],[some 5,none]])
  | _ => throw (IO.userError "host matrix construction did not halt")
