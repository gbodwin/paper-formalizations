import DirectedFlowCutGap.EncodedHeavyVertexOutput

open DirectedFlowCutGap
open RawNonnegativeRational EncodedUnitCostReplication
open EncodedCubeRootThreshold EncodedHeavyVertexPreparation

def endpointHeavyExample : Input 27 :=
  { adjacency := Vector.ofFn fun u => Vector.ofFn fun v => decide (u.val+1=v.val)
    weights := Vector.ofFn fun i => if i.val=0 ∨ i.val=26 then Code.one else ⟨1,16,by decide⟩
    costs := Vector.ofFn fun i => if i.val=8 then Code.ofNat (2^80) else Code.one }

def endpointHeavySmoke : Bool :=
  let result := prepare endpointHeavyExample
  let out := result.1
  let selected := Vector.ofFn (n := out.size) fun i => decide (i.val=7 ∨ i.val=15 ∨ i.val=23)
  let mask := combinedMaskWithCost out selected
  let vertices := (List.range 27).filter fun i => mask.1.toArray[i]!
  out.size==25 && out.labels.toArray.toList.map Fin.val == List.range' 1 25 &&
    out.heavy.toArray[0]! && out.heavy.toArray[26]! && !(out.heavy.toArray[1]!) &&
    out.data.weights.toArray.toList.all (fun q => q.num==2 && q.den==16) &&
    (out.data.costs.toArray[7]?.map (fun q => q.num==2^80 && q.den==1)) == some true &&
    vertices == [0,8,16,24,26] && mask.2==15250 && result.2==28025

def allHeavySmoke : Bool :=
  let D : Input 8 :=
    { adjacency := Vector.replicate 8 (Vector.replicate 8 false)
      weights := Vector.replicate 8 ⟨1,8,by decide⟩
      costs := Vector.replicate 8 (Code.ofNat (2^80)) }
  let out := (prepare D).1
  let selected := Vector.replicate out.size false
  out.size==0 && (combinedMask out selected).toArray.toList.all id

def emptyHeavySmoke : Bool :=
  let D : Input 0 := ⟨#v[],#v[],#v[]⟩
  let out := (prepare D).1
  out.size==0 && (combinedMask out (Vector.replicate out.size false)).toArray.toList == []

def cubeSmoke : Bool :=
  ([0,1,2,7,8,9,26,27,28,64].map ceilCube == [1,1,2,2,2,3,3,3,4,4]) &&
    (thresholdWithCost 0).1.den==4 && (thresholdWithCost 0).2==8 &&
    (thresholdWithCost 27).1.den==12 && (thresholdWithCost 27).2==26

#eval do
  unless cubeSmoke do throw (IO.userError "cube ceiling or rational threshold failed")
  unless endpointHeavySmoke do throw (IO.userError "heavy endpoints, residual arrays or combined mask failed")
  unless allHeavySmoke do throw (IO.userError "inclusive heavy threshold or empty residual failed")
  unless emptyHeavySmoke do throw (IO.userError "empty original heavy input failed")
  IO.println "PASS: cube boundaries, positive zero-size threshold, heavy original endpoints, retained residual labels, exact doubled raw weights, inclusive heavy cutoff, 80-bit costs, actual union mask and empty cases"

example : ceilCube 27=3 := by decide
example : ceilCube 28=4 := by decide
example : (threshold 8).num=1 ∧ (threshold 8).den=8 := by decide
