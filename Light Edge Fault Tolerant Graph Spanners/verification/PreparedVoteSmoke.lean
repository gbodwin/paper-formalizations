import LightEFTSpanners.StoredPreparedHostExecutable
open LightEFTSpanners
open StoredHostPreparation

def hostRecord (id : ℕ) (inc : List StoredEdges.Edge) : Record :=
  ⟨id,inc,⟨[],[[]]⟩⟩
def check (name : String) (n u v h : ℕ) (budget : ℚ) (rs : List Record) (expected : Bool) : IO Unit := do
  let w := List.replicate n (List.replicate n (0:ℚ))
  let b := StoredPreparedHostVote.inputBound n [] [] rs
  let state := Controller.run (StoredPreparedHostVote.transition [] [] w n u v h budget) b
    (.prepare (.prepare (.records rs [])))
  unless state == .halt expected do throw (IO.userError ("FAILED prepared vote "++name))
  IO.println ("PASS prepared vote "++name)

def main : IO Unit := do
  check "empty-positive-threshold" 1 0 0 1 0 [] false
  check "empty-zero-threshold" 1 0 0 0 0 [] true
  check "excluded-host" 2 0 1 1 0 [hostRecord 7 [(0,0)]] false
  check "reversed-unreachable" 2 0 1 1 0 [hostRecord 7 [(1,0)]] true
  check "reachable-self" 1 0 0 1 0 [hostRecord 7 [(0,0)]] false
  check "negative-budget-self" 1 0 0 1 (-1) [hostRecord 7 [(0,0)]] true
  check "distinct-equal-data" 2 0 1 2 0 [hostRecord 7 [(0,1)],hostRecord 8 [(1,0)]] true
  check "incidence-repetition-counts-once" 2 0 1 2 0 [hostRecord 7 [(0,1),(1,0)]] false
