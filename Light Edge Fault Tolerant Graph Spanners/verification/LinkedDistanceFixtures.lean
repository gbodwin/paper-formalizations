import LightEFTSpanners.LinkedDistanceExecutable
open LightEFTSpanners.LinkedDistance

def linkedPath : Matrix := [[none,some (1/3),none],[some (1/3),none,some (1/3)],[none,some (1/3),none]]
def zeroPath : Matrix := [[none,some 0,none],[some 0,none,some 0],[none,some 0,none]]
def empty3 : Matrix := [[none,none,none],[none,none,none],[none,none,none]]
def actualHalt (n : ℕ) (M : Matrix) (u v : ℕ) (b : ℚ) : Bool :=
  match run n M u v b (bound n) (.init n 0 []) with
  | .halt _ => true
  | _ => false

def linkedFixtures : List (String×Bool) := [
 ("empty domain halts",actualHalt 0 [] 0 0 0),
 ("empty domain lookup false",!execute 0 [] 0 0 0),
 ("singleton zero-distance",execute 1 [[none]] 0 0 0),
 ("rational two-edge path",execute 3 linkedPath 0 2 (2/3)),
 ("reverse orientation",execute 3 linkedPath 2 0 (2/3)),
 ("strict threshold",!execute 3 linkedPath 0 2 (1/2)),
 ("unreachable endpoint",!execute 3 empty3 0 2 100),
 ("zero empty walk",execute 3 empty3 1 1 0),
 ("negative budget",!execute 3 empty3 1 1 (-1)),
 ("zero-weight route",execute 3 zeroPath 0 2 0),
 ("within proved cubic fuel",actualHalt 3 linkedPath 0 2 (2/3)),
 ("concrete cubic bound",decide (bound 3=76))]
#eval linkedFixtures.forM fun (p : String×Bool) => do
  if p.2=false then throw (IO.userError s!"FAIL: {p.1}")
  IO.println s!"PASS: {p.1}"
