import LightEFTSpanners.StoredFlagBatchExecutable
open LightEFTSpanners

def check (name : String) (xs : StoredFlagBatch.Input) (expected : StoredFlagBatch.Output) : IO Unit := do
  let out := Controller.run StoredFlagBatch.transition (StoredFlagBatch.budget xs) (.next xs [])
  unless out==StoredFlagBatch.State.halt expected do
    throw (IO.userError ("FAIL flag batch "++name++" "++reprStr out))
  IO.println ("PASS flag batch "++name)

def main : IO Unit := do
  check "no-draws" [] []
  check "one-empty-draw" [[]] [[]]
  check "three-empty-draws" [[],[],[]] [[],[],[]]
  check "one-true" [[((0,1),true)]] [[(0,1)]]
  check "one-false" [[((0,1),false)]] [[]]
  check "ordered-distinct" [[((0,1),true)],[((1,2),true)]] [[(0,1)],[(1,2)]]
  check "empty-between" [[((0,1),true)],[],[((2,3),true)]] [[(0,1)],[],[(2,3)]]
  check "mixed-flags" [[((0,1),false),((1,2),true)],[((2,2),true),((3,4),false)]] [[(1,2)],[(2,2)]]
  check "duplicate-occurrences" [[((0,1),true),((0,1),true)],[((0,1),true)]] [[(0,1),(0,1)],[(0,1)]]
  check "large-reversed" [[((100,200),true)],[((200,100),true),((7,7),true)]] [[(100,200)],[(200,100),(7,7)]]
