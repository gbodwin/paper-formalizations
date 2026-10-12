import LightEFTSpanners.StoredCandidateBankEncoding
open LightEFTSpanners

def record (id : ℕ) (es : List StoredEdges.Edge) : StoredHostPreparation.Record := ⟨id,es,⟨[],[]⟩⟩
def check (name : String) (W : StoredRecords.Weights) (t : ℚ)
    (rs : List StoredCandidatePreparation.Input) (out : List StoredCandidates.Input) : IO Unit := do
  let s := Controller.run (StoredCandidateBankPreparation.transition W t)
    (StoredCandidateBankPreparation.inputBound rs) (.inputs rs [])
  unless s == .halt out do throw (IO.userError ("FAILED candidate bank "++name))
  IO.println ("PASS candidate bank "++name)
def main : IO Unit := do
  check "empty" [] 1 [] []
  check "matrix-row-and-column" [[0,3],[5,7]] 2 [⟨(1,0),[]⟩] [⟨(1,0),10,[]⟩]
  check "missing-row-zero" [] 2 [⟨(2,1),[]⟩] [⟨(2,1),0,[]⟩]
  check "missing-column-zero" [[3]] 2 [⟨(0,2),[]⟩] [⟨(0,2),0,[]⟩]
  check "filtered-host-order" [[0,1],[1,0]] 3
    [⟨(0,1),[record 2 [(0,0)],record 3 [(1,0)],record 4 [(0,1)]]⟩]
    [⟨(0,1),3,[(record 3 []).host,(record 4 []).host]⟩]
  check "candidate-order" [[1,2],[3,4]] (-1)
    [⟨(0,1),[]⟩,⟨(1,0),[]⟩] [⟨(0,1),-2,[]⟩,⟨(1,0),-3,[]⟩]
