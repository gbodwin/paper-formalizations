import DirectedFlowCutGap.EncodedUniformOutput
import DirectedFlowCutGap.EncodedInputSizing

open DirectedFlowCutGap
open RawNonnegativeRational EncodedUnitCostReplication
open EncodedUniformWeightParameters EncodedUniformChain EncodedUniformOutput

def uniformExample (weights : Vector Code 3) : Input 3 :=
  { adjacency := Vector.ofFn fun u => Vector.ofFn fun v => decide (u.val+1=v.val)
    weights := weights
    costs := Vector.replicate 3 Code.one }

def chainSmoke : Bool :=
  let D := uniformExample #v[Code.zero,Code.one,Code.zero]
  match EncodedUniformChain.reduce D with
  | .trivial _ _ => false
  | .expanded p out _ =>
    let a := out.data.adjacency.toArray
    let selected := Vector.ofFn (n := out.size) fun i => decide (i.val=5)
    let result := originalMaskWithCost out selected
    out.size == 17 && out.cutoff == 9 &&
      p.counts.toArray.toList == [1,9,1,1,1,1,1,1,1] &&
      out.data.weights.toArray.toList.all (fun q => q.num==1 && q.den==9) &&
      (a[11]?.bind fun row => row.toArray[1]?) == some true &&
      (a[1]?.bind fun row => row.toArray[2]?) == some true &&
      (a[9]?.bind fun row => row.toArray[16]?) == some true &&
      (a[1]?.bind fun row => row.toArray[16]?) == some false &&
      (a[12]?.bind fun row => row.toArray[15]?) == some true &&
      result.1.toArray.toList == [false,true,false] && result.2 == 1682

def nonintegerCutoffSmoke : Bool :=
  match EncodedUniformChain.reduce (uniformExample #v[⟨1,4,by decide⟩,Code.one,Code.zero]) with
  | .trivial _ _ => false
  | .expanded p out _ => out.size==17 && out.cutoff==8 &&
      p.counts.toArray.toList == [2,8,1,1,1,1,1,1,1]

def clippedHeavySmoke : Bool :=
  match EncodedUniformChain.reduce (uniformExample (Vector.replicate 3 (Code.ofNat (2^80)))) with
  | .trivial _ _ => false
  | .expanded p out _ => out.size==15 && out.cutoff==3 &&
      p.counts.toArray.toList == [3,3,3,1,1,1,1,1,1]

def smallMassSmoke : Bool :=
  let tiny : Code := ⟨1,2^80,by decide⟩
  match EncodedUniformChain.reduce (uniformExample #v[Code.zero,tiny,Code.zero]) with
  | .trivial mask _ => mask.toArray.toList == [false,false,false]
  | .expanded _ _ _ => false

def emptyUniformSmoke : Bool :=
  let D : Input 0 := ⟨#v[],#v[],#v[]⟩
  match EncodedUniformChain.reduce D with
  | .trivial mask _ => mask.toArray.toList == []
  | .expanded _ _ _ => false

def retainedSizeCompositionSmoke : Bool :=
  let D : Input 2 :=
    { adjacency := Vector.ofFn fun u => Vector.ofFn fun v => decide (u.val=0 ∧ v.val=1)
      weights := #v[Code.one,Code.zero]
      costs := #v[Code.one,Code.one] }
  let k : Vector ℕ 2 := #v[2,1]
  let replica := EncodedUnitCostReplication.materialize D k
  let sized := EncodedInputSizing.retainReplica replica
  match EncodedUniformChain.reduce (n := sized.size) sized.data with
  | .trivial _ _ => false
  | .expanded _ chain _ =>
    let selected := Vector.ofFn (n := chain.size) fun i => decide (i.val=0)
    let uniformOriginal := originalMask chain selected
    let restored := sized.restoreMaskWithCost uniformOriginal
    let original := fullFiberMask k replica.labels restored.1
    sized.size==3 && sized.work==12 && chain.size==17 && chain.cutoff==5 &&
      uniformOriginal.toArray.toList == [true,false,false] && restored.2==3 &&
      original.toArray.toList == [false,false]

#eval do
  unless chainSmoke do throw (IO.userError "chain edges, ports or any-copy output failed")
  unless nonintegerCutoffSmoke do throw (IO.userError "nonintegral reciprocal ceiling failed")
  unless clippedHeavySmoke do throw (IO.userError "heavy clipping failed")
  unless smallMassSmoke do throw (IO.userError "tiny positive mass branch failed")
  unless retainedSizeCompositionSmoke do throw (IO.userError "retained-size composition failed")
  unless emptyUniformSmoke do throw (IO.userError "empty uniform input failed")
  IO.println "PASS: actual uniform chain/port edges, first/last restrictions, any-copy original mask, exact and nonintegral cutoffs, 80-bit heavy/tiny weights, low-mass and empty branches"

example : (Code.one.div (Code.mk 5 36 (by decide))).ceil = 8 := by decide
example : (Code.one.div (Code.mk 1 9 (by decide))).ceil = 9 := by decide
