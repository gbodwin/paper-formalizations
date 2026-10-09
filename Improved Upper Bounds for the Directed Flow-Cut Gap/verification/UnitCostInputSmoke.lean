import DirectedFlowCutGap.EncodedUnitCostReplication

open DirectedFlowCutGap
open RawNonnegativeRational EncodedUnitCostReplication

def replicationExample (cost : ℕ) : Input 6 :=
  { adjacency := Vector.ofFn fun u => Vector.ofFn fun v =>
      decide ((u.val=2 ∧ v.val=0) ∨ (u.val=0 ∧ v.val=1) ∨ (u.val=1 ∧ v.val=5))
    weights := #v[⟨1,2,by decide⟩,Code.one,Code.zero,Code.zero,Code.zero,Code.zero]
    costs := #v[Code.ofNat cost,Code.one,Code.zero,Code.zero,Code.zero,Code.zero] }

def zeroExample : Input 6 := { replicationExample 8 with costs := Vector.replicate 6 Code.zero }
def emptyExample : Input 0 := ⟨#v[],#v[],#v[]⟩

def replicationSmoke (cost : ℕ) : Bool :=
  let D := replicationExample cost
  match D.reduce with
  | .zero _ _ => false
  | .replicated _ k out _ =>
    let N := out.weights.toArray.size
    let partialMask := Vector.ofFn (n := (cloneList k).length) fun i => decide (i.val=0)
    let whole := Vector.ofFn (n := (cloneList k).length) fun i => decide (i.val<2)
    let p := fullFiberMask k out.labels partialMask
    let q := fullFiberMask k out.labels whole
    k.toArray.toList == [2,1,1,1,1,1] && N == 7 &&
    !(p[0]) && q[0] && !(q[1]) &&
    (out.adjacency.toArray[0]?.bind (fun row => row.toArray[2]?)) == some true &&
    (out.adjacency.toArray[1]?.bind (fun row => row.toArray[2]?)) == some true &&
    (out.adjacency.toArray[2]?.bind (fun row => row.toArray[0]?)) == some false &&
    out.costs.toArray.toList.all (fun c => c.num == 1 && c.den == 1)

def zeroSmoke : Bool :=
  match zeroExample.reduce with
  | .zero mask _ => mask.toArray.toList == [true,true,false,false,false,false]
  | .replicated _ _ _ _ => false

def emptySmoke : Bool :=
  match emptyExample.reduce with
  | .zero mask _ => mask.toArray.toList == []
  | .replicated _ _ _ _ => false

#eval do
  unless replicationSmoke 8 do throw (IO.userError "ordinary replication smoke failed")
  unless replicationSmoke (2^80) do throw (IO.userError "large binary cost smoke failed")
  unless zeroSmoke do throw (IO.userError "zero-objective mask smoke failed")
  unless emptySmoke do throw (IO.userError "empty input smoke failed")
  IO.println "PASS: ordinary and 80-bit costs, exact clone counts, complete-fiber edges, partial/full fiber masks, zero and empty branches"

example : (Code.mk 7 3 (by decide)).ceil = 3 := by decide
example : (Code.mk 0 7 (by decide)).ceil = 0 := by decide
example : (Code.mk 9 3 (by decide)).ceil = 3 := by decide
