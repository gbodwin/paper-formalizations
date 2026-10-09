import DirectedFlowCutGap.RetainedCandidateSolver
import DirectedFlowCutGap.RetainedDemandMask
import DirectedFlowCutGap.RetainedSampledExecution

set_option synthInstance.maxSize 8192

open DirectedFlowCutGap RetainedGridState RetainedTapeInput RetainedSampledExecution
open scoped NNReal

/-- Every directed nonloop edge except 0→2. Exactly one demand remains, and
its only simple internal route forces vertex 1 into the final cut. -/
private def adjacency : PairFlags 3 :=
  #v[#v[false,true,false],#v[true,false,true],#v[true,true,false]]

private def zeroPermutation : (k : ℕ) → FinitePermutationSampler.Tape k
  | 0 => ()
  | k+1 => (0,zeroPermutation k)

private def zeroCells : (k : ℕ) → FiniteGridSampler.Cells 1 k
  | 0 => ()
  | k+1 => (0,zeroCells k)

/-- This checks one concrete lawful finite-tape realization. The state counts
actual callback invocations, independently of the retained input log. -/
private def sample (a : PairFlags 3) : StateM ℕ (RetainedTapeInput.Tape 1 a) := do
  modify (·+1)
  pure (zeroPermutation _,zeroCells _)

#eval do
  let F := CandidateEnumeration.make 3 1
  let s := RetainedDemandMask.initial (RetainedCandidateSolver.graph adjacency)
    F.base.enumeration 1 (by decide)
  unless (remainingSet s.data.remaining).card == 1 && flag s.data.remaining (0,2) do
    throw (IO.userError "focused Boolean graph did not produce exactly demand (0,2)")
  let Q := RetainedCandidateSolver.optimizer adjacency F
    (CandidateEnumeration.fin_vertices 3) (by decide : 0<1)
  let (out,calls) := (runSampled sample Q (by decide : 0<1)
    (integerCutOracle (G := RetainedCandidateSolver.graph adjacency) (by decide) F.base.enumeration)
    2 5 5 s).run 0
  unless out.result.work.restarts > 0 do
    throw (IO.userError "sampled run did not install a genuine candidate family")
  unless out.result.work.rounds > 0 do
    throw (IO.userError "sampled run did not execute an integer level cut")
  unless out.result.work.families == 1+out.result.work.restarts+out.result.work.rounds do
    throw (IO.userError "initial/restart/round family call accounting mismatch")
  unless out.result.cache.optimal == 0 do
    throw (IO.userError "sampled run did not reach terminal zero optimum")
  unless out.result.cache.state.data.cut.toArray == #[false,true,false] do
    throw (IO.userError "sampled run did not cut precisely the unique internal vertex")
  unless (remainingSet out.result.cache.state.data.remaining).card == 0 do
    throw (IO.userError "processed original demand label survived")
  unless out.inputs.length == 1 && calls == 1 do
    throw (IO.userError "terminal epochs were sampled or the input log was replayed")
  IO.println s!"PASS nonterminal retained sampled execution: {repr out.result.work}; sampled epochs={calls}; cut={out.result.cache.state.data.cut.toArray}"
