import LightEFTSpanners.StoredRepetitionProgram
open LightEFTSpanners

def check (n s expected : ℕ) : IO Unit := do
  let out := Controller.run StoredRepetitions.transition 4 (.offset n s)
  unless out==StoredRepetitions.State.halt expected do
    throw (IO.userError ("FAIL repetition "++reprStr (n,s,out)))
  IO.println ("PASS repetition "++reprStr (n,s,expected))

def main : IO Unit := do
  check 0 0 1
  check 0 100 1
  check 1 0 161
  check 2 0 321
  check 3 1 577
  check 4 2 897
  check 10 10 4801
  check 100 3 25601
