import LightEFTSpanners.StoredComponentCandidateExecutable
open LightEFTSpanners

def hostInput (id : ℕ) (vs : List ℕ) (draws : List (List StoredEdges.Edge)) : StoredComponentRecord.Input :=
  ⟨id,vs,⟨[],draws⟩⟩
def check (name : String) (n h : ℕ) (t : ℚ) (W : StoredRecords.Weights)
    (rs : List StoredComponentCandidate.Input) (expected : List StoredEdges.Edge) : IO Unit := do
  let b := StoredComponentCandidates.inputBound n [] [] rs
  let actual := Controller.run (StoredComponentCandidates.transition [] [] W n h t) b (.prepare (.inputs rs []))
  unless actual == .select (.halt expected) do throw (IO.userError ("FAILED component preparation "++name))
  IO.println ("PASS component preparation "++name)

def main : IO Unit := do
  check "empty" 1 1 1 [[0]] [] []
  check "empty-component" 2 1 1 [[0,1],[1,0]] [⟨(0,1),[hostInput 4 [] [[]]]⟩] []
  check "disjoint-singletons" 2 1 1 [[0,1],[1,0]]
    [⟨(0,1),[hostInput 4 [0] [[]],hostInput 5 [1] [[]]]⟩] []
  check "same-component" 2 1 1 [[0,1],[1,0]] [⟨(0,1),[hostInput 4 [1,0] [[]]]⟩] [(0,1)]
  check "repeated-vertices-one-host" 2 2 1 [[0,1],[1,0]] [⟨(0,1),[hostInput 4 [0,1,0] [[]]]⟩] []
  check "two-distinct-component-labels" 2 2 1 [[0,1],[1,0]]
    [⟨(0,1),[hostInput 4 [0,1] [[]],hostInput 5 [1,0] [[]]]⟩] [(0,1)]
  check "changing-selected-list" 2 1 1 [[0,1],[1,0]]
    [⟨(0,1),[hostInput 4 [0,1] [[(0,1)]]]⟩,⟨(0,1),[hostInput 4 [0,1] [[(0,1)]]]⟩] [(0,1)]
  check "negative-self-budget" 1 1 (-1) [[1]] [⟨(0,0),[hostInput 4 [0] [[]]]⟩] [(0,0)]
