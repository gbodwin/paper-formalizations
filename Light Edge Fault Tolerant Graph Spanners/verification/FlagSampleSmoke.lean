import LightEFTSpanners.StoredFlagSampleExecutable
open LightEFTSpanners

def check (name : String) (xs : StoredFlagSample.Input) (expected : List StoredEdges.Edge) : IO Unit := do
  let out := Controller.run StoredFlagSample.transition (StoredFlagSample.bound xs) (.scan xs [])
  unless out==StoredFlagSample.State.halt expected do
    throw (IO.userError ("FAIL flag sample "++name++" "++reprStr out))
  IO.println ("PASS flag sample "++name)

def main : IO Unit := do
  check "empty" [] []
  check "false" [((0,1),false)] []
  check "true" [((0,1),true)] [(0,1)]
  check "loop-retained" [((1,1),true)] [(1,1)]
  check "all-false" [((0,1),false),((1,2),false),((2,2),false)] []
  check "all-true" [((0,1),true),((1,2),true),((2,2),true)] [(0,1),(1,2),(2,2)]
  check "alternating" [((0,1),true),((1,2),false),((2,3),true)] [(0,1),(2,3)]
  check "reversed-identities" [((1,0),true),((0,1),true)] [(1,0),(0,1)]
  check "duplicate-cells" [((0,1),false),((0,1),true),((0,1),true)] [(0,1),(0,1)]
  check "large-labels" [((100,200),true),((200,300),false)] [(100,200)]
