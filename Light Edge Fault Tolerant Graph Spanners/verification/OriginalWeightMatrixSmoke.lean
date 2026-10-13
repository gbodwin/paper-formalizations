import LightEFTSpanners.StoredOriginalWeightMatrixEncoding
open LightEFTSpanners

def check (name : String) (n : ℕ) (bank : StoredOriginalWeightLookup.Bank) (expected : StoredRecords.Weights) : IO Unit := do
  let out := Controller.run (StoredOriginalWeightMatrix.transition n bank)
    (StoredOriginalWeightMatrix.bound n bank.length) (.rows 0 n [])
  unless out==.halt expected do throw (IO.userError ("FAIL original weights "++name++" "++reprStr out))
  IO.println ("PASS original weights "++name)

def main : IO Unit := do
  check "empty-universe" 0 [] []
  check "zero-default" 2 [] [[0,0],[0,0]]
  check "forward" 2 [((0,1),7)] [[0,7],[7,0]]
  check "reversed" 2 [((1,0),3)] [[0,3],[3,0]]
  check "first-duplicate" 2 [((0,1),2),((1,0),9)] [[0,2],[2,0]]
  check "first-zero" 2 [((1,0),0),((0,1),9)] [[0,0],[0,0]]
  check "diagonal" 2 [((0,0),5),((1,1),6)] [[5,0],[0,6]]
  check "negative-rational" 2 [((0,1),-3/2)] [[0,-3/2],[-3/2,0]]
  check "late-match" 2 [((3,4),8),((1,0),11)] [[0,11],[11,0]]
  check "three-by-three" 3 [((0,2),4),((1,2),6),((1,1),2)] [[0,0,4],[0,2,6],[4,6,0]]
