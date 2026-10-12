import LightEFTSpanners.StoredPreparedHostRecords
open LightEFTSpanners
open StoredHostPreparation

def sample (id : ℕ) (edges : List StoredEdges.Edge) : Record :=
  ⟨id,edges,⟨[(id,id+1)],[[],[(id+1,id)]]⟩⟩
def test (name : String) (q : StoredEdges.Edge) (rs expected : List Record) : IO Unit := do
  let k := inputBound rs
  let actual := Controller.run (transition q) k (.records rs [])
  unless actual==.halt expected do throw (IO.userError ("selection "++name))
  let p := StoredPreparedHostRecords.inputBound rs
  let records := Controller.run (StoredPreparedHostRecords.transition q) p (.prepare (.records rs []))
  unless records==.halt (expected.map Record.host) do throw (IO.userError ("records "++name))
  IO.println ("PASS prepared hosts "++name)

def main : IO Unit := do
  test "empty" (1,2) [] []
  test "reversed-incidence" (1,2) [sample 7 [(2,1)]] [sample 7 [(2,1)]]
  test "none" (1,2) [sample 7 [(2,3)],sample 8 []] []
  test "stable-order" (1,2) [sample 7 [(1,2)],sample 8 [],sample 9 [(2,1)]] [sample 7 [(1,2)],sample 9 [(2,1)]]
  test "duplicate-incidence" (1,2) [sample 7 [(1,2),(2,1)]] [sample 7 [(1,2),(2,1)]]
  let a : Record := ⟨11,[(1,2)],⟨[],[[]]⟩⟩
  let b : Record := ⟨12,[(2,1)],⟨[],[[]]⟩⟩
  test "distinct-labels-identical-data" (1,2) [a,b] [a,b]
