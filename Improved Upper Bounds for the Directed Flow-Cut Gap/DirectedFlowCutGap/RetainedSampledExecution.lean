import DirectedFlowCutGap.RetainedTapeInput

/-!
# Single-pass adaptive retained execution with finite draws

The caller supplies one finite-tape sampling action for the current active
mask. This interpreter stabilizes and scans each actual state only once. It
retains the consumed materialized inputs as a log; the log is never replayed
by the interpreter. Instantiating the action with the exact primitive PMF gives
the law proved in `RetainedExecutionLaw`. An actual fair-bit implementation of
the sampling callback is a separate obligation.
-/
namespace DirectedFlowCutGap.RetainedSampledExecution

open scoped NNReal
open RetainedGridState IntegerAdaptiveExecution

variable {n L : ℕ} {G : Digraph (Fin n)} {D : Finset (Pair n)}
variable {selector : FlexibleCandidateSchedule.FamilyProvider G D (L : ℝ≥0) → Prop}
variable {H : ∃ P, selector P}

structure LoggedResult (H : ∃ P, selector P) where
  result : Result H
  inputs : List (Input n L)

def finish (a b : Result H) (i : Input n L) (d : LoggedResult H) : LoggedResult H :=
  ⟨⟨d.result.cache, a.work.add (b.work.add d.result.work)⟩, i :: d.inputs⟩

/-- Each continuation receives the cache actually produced by the prior cut.
The mathematical provider occurs only in erased certificates and types. -/
def executeSampled {m : Type → Type} [Monad m]
    (sample : (a : PairFlags n) → m (RetainedTapeInput.Tape L a))
    (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R restartFuel : ℕ) : ℕ → Cache H → m (LoggedResult H)
  | 0, c => pure ⟨stabilize Q R restartFuel c, []⟩
  | epochs + 1, c => do
      let a := stabilize Q R restartFuel c
      if a.cache.optimal == 0 then pure ⟨a, []⟩ else
        let t ← sample a.cache.state.data.remaining
        let i := RetainedTapeInput.materialize hL a.cache.state.data.remaining t
        let b := scan Q hL C R a.cache.state.data.current i.cell i.order a.cache
        let d ← executeSampled sample Q hL C R restartFuel epochs b.cache
        pure (finish a b i d)

/-- The initial optimizer family is computed and counted exactly once. -/
def runSampled {m : Type → Type} [Monad m]
    (sample : (a : PairFlags n) → m (RetainedTapeInput.Tape L a))
    (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (s : Code G D L) : m (LoggedResult H) := do
  let a := start Q s
  let b ← executeSampled sample Q hL C R restartFuel epochs a.cache
  pure ⟨⟨b.result.cache, a.work.add b.result.work⟩, b.inputs⟩

end DirectedFlowCutGap.RetainedSampledExecution
