import DirectedFlowCutGap.EncodedSampledRounding

set_option synthInstance.maxSize 8192

open DirectedFlowCutGap RetainedGridState

private def zeroPermutation : (k : ℕ) → FinitePermutationSampler.Tape k
  | 0 => ()
  | k+1 => (0,zeroPermutation k)

private def zeroCells : (k : ℕ) → FiniteGridSampler.Cells 1 k
  | 0 => ()
  | k+1 => (0,zeroCells k)

private def patternCells : (k : ℕ) → FiniteGridSampler.Cells 4 k
  | 0 => ()
  | k+1 => (⟨k%4,Nat.mod_lt _ (by decide)⟩,patternCells k)

private def chargedSample (a : PairFlags 1) : StateM ℕ (RetainedTapeInput.Tape 1 a × ℕ) := do
  modify (·+1)
  pure ((zeroPermutation _,zeroCells _),4000)

#eval do
  let mask : PairFlags 2 := #v[#v[true,true],#v[false,true]]
  let tape : RetainedTapeInput.Tape 4 mask := (zeroPermutation _,patternCells _)
  let out := EncodedTapeMaterialization.materialize (by decide : 0<4) mask tape
  unless out.1.order == [(0,0),(0,1),(1,1)] do
    throw (IO.userError "retained active dictionary or permutation order changed")
  unless out.1.cell (0,0) == 2 && out.1.cell (0,1) == 1 &&
      out.1.cell (1,0) == 0 && out.1.cell (1,1) == 0 do
    throw (IO.userError "forward/inverse active enumeration or cell decoding changed")
  unless out.2 == 1393 && out.2 ≤ EncodedTapeMaterialization.materializationBound 2 do
    throw (IO.userError "materialization copy/lookup charge changed")
  IO.println s!"PASS active mask, permutation, independent cells, inactive zero and full materialization charge={out.2}"

#eval do
  let adjacency : PairFlags 1 := #v[#v[false]]
  let F := CandidateEnumeration.make 1 1
  let s := RetainedDemandMask.initial (EncodedIntegerShortestPaths.graph adjacency)
    F.base.enumeration 1 (by decide : 0<1)
  let (out,calls) := (EncodedSampledRounding.runSampled adjacency F
    (CandidateEnumeration.fin_vertices 1) (by decide : 0<1) chargedSample 2 3 5 s).run 0
  unless out.operations == 156 && out.sampling == 0 && calls == 0 do
    throw (IO.userError "terminal sampler effects or exact full charge changed")
  unless out.logged.inputs.isEmpty && out.logged.result.work.families == 1 &&
      out.logged.result.work.candidates == 0 && out.logged.result.cache.optimal == 0 do
    throw (IO.userError "terminal logged result changed")
  IO.println s!"PASS fully charged terminal sampled entry; operations={out.operations}; calls={calls}"
