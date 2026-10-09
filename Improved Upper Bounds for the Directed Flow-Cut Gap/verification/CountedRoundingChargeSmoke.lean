import DirectedFlowCutGap.EncodedRoundingRuntime

set_option synthInstance.maxSize 8192
open DirectedFlowCutGap RetainedGridState

#eval do
  let adjacency : PairFlags 1 := #v[#v[false]]
  let F := CandidateEnumeration.make 1 1
  let s := RetainedDemandMask.initial (EncodedIntegerShortestPaths.graph adjacency)
    F.base.enumeration 1 (by decide : 0<1)
  let out := EncodedRoundingRuntime.run adjacency F (CandidateEnumeration.fin_vertices 1)
    (by decide : 0<1) 2 3 [] s
  unless out.2 == 152 do throw (IO.userError "terminal full charge changed")
  unless out.1.work.families == 1 && out.1.work.candidates == 0 &&
      out.1.work.gates == 3 && out.1.work.massScans == 1 do
    throw (IO.userError "terminal events changed")
  unless out.2 ≤ EncodedRoundingRuntime.price 1 1 out.1.work+1 do
    throw (IO.userError "terminal charged bound failed")
  let mask : PairFlags 3 := #v[#v[false,false,true],#v[false,false,false],#v[false,false,false]]
  let zeroCut : Flags 3 := #v[false,false,false]
  let weights : Family 3 := Vector.replicate 3 (Vector.replicate 3 (Vector.replicate 3 1))
  let mass := EncodedRoundingState.mass mask zeroCut weights
  unless mass.1 == 3 && mass.2 == 407 do throw (IO.userError "retained mass charge failed")
  let state : Data 3 := ⟨mask,zeroCut,weights,1,mass.1⟩
  let next := EncodedRoundingState.roundData state (0,2) #v[false,true,false]
  unless next.1.current == 0 && next.2 == 691 &&
      next.1.cut.toArray == #[false,true,false] do
    throw (IO.userError "round materialization charge failed")
  IO.println s!"PASS executed full terminal charge={out.2}, retained mass={mass.2}, erase/union/round={next.2}"
