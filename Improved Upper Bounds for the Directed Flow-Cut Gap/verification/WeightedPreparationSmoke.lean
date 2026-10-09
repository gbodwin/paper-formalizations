import DirectedFlowCutGap.EncodedPreparationOutput

open DirectedFlowCutGap
open RawNonnegativeRational EncodedUnitCostReplication EncodedUnitCostPreparation

def portExample (cost : ℕ) : Input 3 :=
  { adjacency := Vector.ofFn fun u => Vector.ofFn fun v =>
      decide ((u.val=0 ∧ v.val=2) ∨ (u.val=2 ∧ v.val=1) ∨ (u.val=0 ∧ v.val=0))
    weights := #v[Code.zero,⟨1,4,by decide⟩,Code.one]
    costs := #v[Code.zero,Code.ofNat cost,Code.zero] }

def removedBridgeExample (cost : ℕ) : Input 4 :=
  { adjacency := Vector.ofFn fun u => Vector.ofFn fun v => decide (u.val+1=v.val)
    weights := #v[Code.zero,⟨1,16,by decide⟩,Code.one,Code.zero]
    costs := #v[Code.zero,Code.ofNat (2^80),Code.ofNat cost,Code.zero] }

def preparationSmoke (cost : ℕ) : Bool :=
  let reduction := prepareAndReduce (portExample cost)
  let out := reduction.prepared
  let a := out.data.adjacency.toArray
  out.size == 8 && out.ports.toArray.toList.map Fin.val == [1,2,3,4,5,6,7,8] &&
  (a[2]?.bind fun row => row.toArray[5]?) == some true &&
  (a[2]?.bind fun row => row.toArray[6]?) == some false &&
  match reduction.reduced with
  | .zero _ _ => false
  | .replicated _ k replica _ =>
    let N := replica.labels.toArray.size
    let partialMask := Vector.cast replica.labels.size_toArray
      (Vector.ofFn (n := N) fun i => decide (i.val=0 ∨ i.val=2))
    let whole := Vector.cast replica.labels.size_toArray
      (Vector.ofFn (n := N) fun i => decide (i.val<3))
    let p := out.pullbackSampleWithCost k replica partialMask
    let q := out.pullbackSampleWithCost k replica whole
    k.toArray.toList == [2,1,1,1,1,1,1,1] && N == 9 &&
      p.1.toArray.toList == [false,false,true] &&
      q.1.toArray.toList == [false,true,true] && p.2 == q.2

def removedBridgeSmoke : Bool :=
  let out := build (removedBridgeExample 5)
  let a := out.data.adjacency.toArray
  out.size == 9 && out.ports.toArray.toList.map Fin.val == [2,4,5,6,7,8,9,10,11] &&
    (a[1]?.bind fun row => row.toArray[0]?) == some true &&
    (a[0]?.bind fun row => row.toArray[8]?) == some true &&
    (a[1]?.bind fun row => row.toArray[8]?) == some false

def zeroPreparationSmoke : Bool :=
  let reduction := prepareAndReduce (removedBridgeExample 0)
  match reduction.reduced with
  | .zero mask _ => (reduction.prepared.pullbackMask mask).toArray.toList == [false,false,true,false]
  | .replicated _ _ _ _ => false

def replacementSmoke : Bool :=
  let out := build (portExample 1000)
  let costs : Vector Code 3 := #v[Code.zero,Code.ofNat (2^80),Code.ofNat 7]
  let refreshed := out.replaceCosts costs
  let rebuilt := build {portExample 1000 with costs := costs}
  refreshed.size == rebuilt.size &&
    refreshed.ports.toArray.toList.map Fin.val == rebuilt.ports.toArray.toList.map Fin.val &&
    refreshed.data.adjacency.toArray.toList.map (fun row => row.toArray.toList) ==
      rebuilt.data.adjacency.toArray.toList.map (fun row => row.toArray.toList) &&
    refreshed.data.weights.toArray.toList.map (fun q => (q.num,q.den)) ==
      rebuilt.data.weights.toArray.toList.map (fun q => (q.num,q.den)) &&
    refreshed.data.costs.toArray.toList.map (fun q => (q.num,q.den)) ==
      rebuilt.data.costs.toArray.toList.map (fun q => (q.num,q.den)) &&
    refreshed.work == 500

def emptyOriginal : Input 0 := ⟨#v[],#v[],#v[]⟩

def emptyPreparationSmoke : Bool :=
  let reduction := prepareAndReduce emptyOriginal
  reduction.prepared.size == 0 &&
  match reduction.reduced with
  | .zero mask _ => (reduction.prepared.pullbackMask mask).toArray.toList == []
  | .replicated _ _ _ _ => false

#eval do
  unless preparationSmoke 1000 do throw (IO.userError "original input preparation/positive pullback failed")
  unless preparationSmoke (2^80) do throw (IO.userError "80-bit original cost preparation failed")
  unless removedBridgeSmoke do throw (IO.userError "removed interior shortcut or surviving interior exclusion failed")
  unless zeroPreparationSmoke do throw (IO.userError "zero objective original mask failed")
  unless replacementSmoke do throw (IO.userError "retained cost replacement failed")
  unless emptyPreparationSmoke do throw (IO.userError "empty original input failed")
  IO.println "PASS: original rational inputs, retained endpoints, removed-interior shortcut, survivor-interior exclusion, actual clone counts, partial/full fiber original masks, 80-bit costs, fixed-array cost replacement, zero and empty branches"

example : EncodedPortPreparation.decodePort (EncodedPortPreparation.encodePort
    (TerminalPorts.core (1 : Fin 3))) = TerminalPorts.core (1 : Fin 3) := by decide
example : (build emptyOriginal).size = 0 := by decide
example : (build emptyOriginal).data.totals.objective.num = 0 := by decide
