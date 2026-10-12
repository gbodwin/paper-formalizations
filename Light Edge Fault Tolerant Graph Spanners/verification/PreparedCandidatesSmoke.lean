import LightEFTSpanners.StoredPreparedCandidateExecutable
open LightEFTSpanners

def rec (id : ℕ) (inc : List StoredEdges.Edge) : StoredHostPreparation.Record :=
  ⟨id,inc,⟨[],[[]]⟩⟩
def check (name : String) (n h : ℕ) (t : ℚ) (w : StoredRecords.Weights)
    (rs : List StoredCandidatePreparation.Input) (expected : List StoredEdges.Edge) : IO Unit := do
  let b := StoredPreparedCandidates.inputBound n [] [] rs
  let actual := Controller.run (StoredPreparedCandidates.transition [] [] w n h t) b (.prepare (.inputs rs []))
  unless actual == .select (.halt expected) do throw (IO.userError ("FAILED prepared candidates "++name))
  IO.println ("PASS prepared candidates "++name)

def main : IO Unit := do
  check "empty" 1 1 1 [[0]] [] []
  check "zero-threshold" 2 0 1 [[0,1],[1,0]] [⟨(0,1),[]⟩] [(0,1)]
  check "excluded-incidence" 2 1 1 [[0,1],[1,0]] [⟨(0,1),[rec 7 [(0,0)]]⟩] []
  check "reverse-incidence" 2 1 1 [[0,1],[1,0]] [⟨(0,1),[rec 7 [(1,0)]]⟩] [(0,1)]
  check "same-selected-state" 2 1 1 [[0,1],[1,0]]
    [⟨(0,1),[⟨7,[(0,1)],⟨[],[[(0,1)]]⟩⟩]⟩,
     ⟨(0,1),[⟨7,[(0,1)],⟨[],[[(0,1)]]⟩⟩]⟩] [(0,1)]
  check "negative-budget" 1 1 (-1) [[1]] [⟨(0,0),[rec 7 [(0,0)]]⟩] [(0,0)]
  check "positive-self-budget" 1 1 1 [[2]] [⟨(0,0),[rec 7 [(0,0)]]⟩] []
  check "two-distinct-host-labels" 2 2 1 [[0,1],[1,0]]
    [⟨(0,1),[rec 7 [(0,1)],rec 8 [(1,0)]]⟩] [(0,1)]
