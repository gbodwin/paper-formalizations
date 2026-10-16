import LightEFTSpanners.StoredHostMachine
open LightEFTSpanners.StoredHosts
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredHosts.successes
  let some c := env.find? name | throwError "successes missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "successes not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: successes safe, total, computable, explicit List.rec, no partial companion"
example (vote : Input → Bool) : successes vote [] = 0 := rfl
example (vote : Input → Bool) (R : Input) (rs : List Input) :
    successes vote (R::rs) = (if vote R then 1 else 0)+successes vote rs := rfl
#eval do
  let e : Input := ⟨[],[]⟩
  let a : Input := ⟨[(0,1)],[]⟩
  let b : Input := ⟨[],[[]]⟩
  let c : Input := ⟨[(0,0),(9,8)],[[(9,8)],[]]⟩
  let d : Input := ⟨[(100000000000000000000,1)],[[(100000000000000000000,1)],[(100000000000000000000,1)]]⟩
  let rs := [e,a,b,c,d]
  let checks := [
    decide (successes (fun _ => true) [] = 0),
    decide (successes (fun _ => false) [] = 0),
    decide (successes (fun _ => true) [e] = 1),
    decide (successes (fun _ => false) [e] = 0),
    decide (successes (fun _ => true) rs = 5),
    decide (successes (fun _ => false) rs = 0),
    decide (successes (fun R => R.edges.isEmpty) rs = 2),
    decide (successes (fun R => R.draws.isEmpty) rs = 2),
    decide (successes (fun R => R.edges.isEmpty || R.draws.isEmpty) rs = 3),
    decide (successes (fun R => R.edges.isEmpty && R.draws.isEmpty) rs = 1),
    decide (successes (fun R => R.edges.any fun x => decide (x.1=x.2)) rs = 1),
    decide (successes (fun R => R.edges.any fun x => decide (x.1=100000000000000000000)) rs = 1),
    decide (successes (fun R => LightEFTSpanners.StoredEdges.contains (1,0) R.edges) rs = 1),
    decide (successes (fun R => decide (2≤R.draws.length)) rs = 2),
    decide (successes (fun R => decide (R.draws.length%2=1)) rs = 1),
    decide (successes (fun R => decide (R=a)) [a,a,b,a] = 3),
    decide (successes (fun _ => false) (List.replicate 32 c) = 0),
    decide (successes (fun _ => true) (List.replicate 32 c) = 32),
    decide (successes (fun R => R.edges.isEmpty) [b,b,a,b,c] = 3),
    decide (successes (fun _ => true) (List.replicate 64 a ++ [e]) = 65)]
  unless checks.all id do throw (IO.userError "Exact arbitrary-vote success-count fixtures failed")
  IO.println s!"PASS: {checks.length} complete host-success count fixtures; empty, constant votes, arbitrary record predicates, loops, duplicate records/draws, huge naturals and long lists"
