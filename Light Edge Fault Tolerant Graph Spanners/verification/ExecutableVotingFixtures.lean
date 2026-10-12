import LightEFTSpanners.ExecutableVotingWork
open LightEFTSpanners LightEFTSpanners.RationalDistance LightEFTSpanners.ExecutableVoting
open SimpleGraph

def path3 : Finset (Sym2 (Fin 3)) := {s(0,1),s(1,2)}
def thirdWeight (_ : Sym2 (Fin 3)) : ℚ := 1/3
theorem third_nonneg : ∀ e,0≤thirdWeight e := by intro e;norm_num [thirdWeight]
def unitWeight (_ : Sym2 (Fin 3)) : ℚ := 1
theorem unit_nonneg : ∀ e,0≤unitWeight e := by intro e;norm_num [unitWeight]

def fixtureResults : List (String × Bool) := [
  ("empty graph has empty output",decide ((edgesWork (n:=0) (j:=0) ∅ (fun _ => 0) (by intro e;norm_num) 1
    (fun _ => ∅) (fun _ => ∅) (fun _ _ _ => []) 1 []).1=∅)),
  ("singleton empty walk",shortTest (graph (∅ : Finset (Sym2 (Fin 1)))) (fun _ => (1:ℚ)) 0 0 0),
  ("rational two-edge path",shortTest (graph path3) thirdWeight 0 2 (2/3)),
  ("strict threshold rejects",!shortTest (graph path3) thirdWeight 0 2 (1/2)),
  ("reverse orientation",shortTest (graph path3) thirdWeight 2 0 (2/3)),
  ("unreachable distinct endpoints",!shortTest (graph (∅ : Finset (Sym2 (Fin 3)))) unitWeight 0 2 100),
  ("empty walk at zero",shortTest (graph (∅ : Finset (Sym2 (Fin 3)))) unitWeight 1 1 0),
  ("negative budget rejects empty walk",!shortTest (graph (∅ : Finset (Sym2 (Fin 3)))) unitWeight 1 1 (-1)),
  ("zero weight path",shortTest (graph path3) (fun _ => 0) 0 2 0),
  ("measured distance value",(coveredWork (graph path3) thirdWeight third_nonneg 2 s(0,2)).1),
  ("measured distance cost",decide ((coveredWork (graph path3) thirdWeight third_nonneg 2 s(0,2)).2=185)),
  ("one actual failing sample inserts",decide ((edgesWork ∅ unitWeight unit_nonneg 1
    (fun _ => (Finset.univ : Finset (Fin 1))) (fun _ => ∅) (fun _ _ _ => [∅]) 1 [s(0,1)]).1={s(0,1)})),
  ("empty samples do not vote",decide ((edgesWork ∅ unitWeight unit_nonneg 1
    (fun _ => (Finset.univ : Finset (Fin 1))) (fun _ => ∅) (fun _ _ _ => []) 1 [s(0,1)]).1=∅)),
  ("two-vote threshold retains empty output",decide ((edgesWork ∅ unitWeight unit_nonneg 1
    (fun _ => (Finset.univ : Finset (Fin 1))) (fun _ => ∅) (fun _ _ _ => [∅]) 2 [s(0,1)]).1=∅)),
  ("seed is retained",decide ((edgesWork path3 unitWeight unit_nonneg 2
    (fun _ => (Finset.univ : Finset (Fin 1))) (fun _ => path3) (fun _ _ _ => [∅]) 1 [s(0,2)]).1=path3))]

def runFixtures : IO Unit :=
  fixtureResults.forM fun (pair : String × Bool) => do
    if pair.2 = false then throw (IO.userError s!"FAIL: {pair.1}")
    IO.println s!"PASS: {pair.1}"
#eval runFixtures
