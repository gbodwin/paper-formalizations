import LightEFTSpanners.SampleVoteExecutable
open LightEFTSpanners SampleRecords SampleVote

def off : Entry := ⟨1,false,false,false,false⟩
def on : Entry := ⟨1,false,true,false,true⟩
def clipped : Entry := ⟨1,true,true,false,true⟩
def hosted : Entry := ⟨1,true,false,true,false⟩
def absent : Records := [[off,off],[off,off]]
def present : Records := [[off,on],[on,off]]
def blocked : Records := [[off,clipped],[clipped,off]]
def inHost : Records := [[off,hosted],[hosted,off]]
def done (n m u v : ℕ) (b : ℚ) (rs : List Records) : Bool :=
  match Controller.run (SampleVote.transition n u v b) (SampleVote.bound n m) (.samples rs 0 0) with
  | .halt _ => true
  | _ => false

def fixtures : List (String×Bool) := [
 ("no draws cannot vote",!SampleVote.execute 2 0 0 1 1 []),
 ("empty vote halts",done 2 0 0 1 1 []),
 ("uncovered draw votes",SampleVote.execute 2 1 0 1 1 [absent]),
 ("covered draw does not vote",!SampleVote.execute 2 1 0 1 1 [present]),
 ("seed-difference clipping removes nonhost",SampleVote.execute 2 1 0 1 1 [blocked]),
 ("host retained despite seed clipping",!SampleVote.execute 2 1 0 1 1 [inHost]),
 ("one of four below 3/8",!SampleVote.execute 2 4 0 1 1 [present,present,present,absent]),
 ("two of four above 3/8",SampleVote.execute 2 4 0 1 1 [present,absent,present,absent]),
 ("three of eight exact threshold",SampleVote.execute 2 8 0 1 1 [present,absent,present,absent,present,absent,present,present]),
 ("negative budget counts empty route failure",SampleVote.execute 2 1 0 0 (-1) [absent]),
 ("zero budget empty route covered",!SampleVote.execute 2 1 0 0 0 [absent]),
 ("reverse endpoint covered",!SampleVote.execute 2 1 1 0 1 [present]),
 ("matrix and distance materialization halts",done 2 8 0 1 1 [present,absent,present,absent,present,absent,present,present]),
 ("actual per-sample bound",decide (SampleVote.perSample 2=57))]
#eval fixtures.forM fun (p : String×Bool) => do
  if p.2=false then throw (IO.userError s!"FAIL: {p.1}")
  IO.println s!"PASS: {p.1}"
