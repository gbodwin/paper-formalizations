import DirectedFlowCutGap.RetainedSampledExecution

/-!
# Observing stateful adaptive sampling without losing the entering ledger

An observable marginal may be state independent even when returned charges
and the physical state are correlated with the sampled result. The generic
PMF identities below retain that distinction. The adaptive controller join
uses a pointwise callback law at every entering physical state; it does not
assume that complete output records or ledgers have finite types.
-/
namespace DirectedFlowCutGap.StatefulSamplerProjection
noncomputable section
variable {S A B : Type}

def observe (p : StateT S PMF A) (s : S) : PMF A := (p.run s).map Prod.fst

theorem observe_pure (a : A) (s : S) : observe (pure a : StateT S PMF A) s = PMF.pure a := by
  change (PMF.pure (a,s)).map Prod.fst = PMF.pure a
  exact PMF.pure_map _ _

/-- A continuation with a state-independent observable law may be composed
without assuming that its physical state is independent of its result. -/
theorem observe_bind (p : StateT S PMF A) (f : A → StateT S PMF B)
    (g : A → PMF B) (h : ∀ a s, observe (f a) s = g a) (s : S) :
    observe (p >>= f) s = (observe p s).bind g := by
  change ((p.run s).bind (fun q => (f q.1).run q.2)).map Prod.fst =
    ((p.run s).map Prod.fst).bind g
  rw [PMF.map_bind,PMF.bind_map]
  congr 1
  funext q
  exact h q.1 q.2

theorem observe_map (p : StateT S PMF A) (f : A → B) (s : S) :
    observe (f <$> p) s = (observe p s).map f := by
  have h := observe_bind p (fun a => pure (f a)) (fun a => PMF.pure (f a))
    (fun a s => observe_pure (f a) s) s
  rw [map_eq_pure_bind]
  exact h


theorem observe_bind_map {C : Type} (p : StateT S PMF A) (f : A → StateT S PMF B)
    (k : A → B → C) (g : A → PMF B)
    (h : ∀ a s, observe (f a) s = g a) (s : S) :
    observe (do let a ← p; let b ← f a; pure (k a b)) s =
      (observe p s).bind (fun a => (g a).map (k a)) := by
  apply observe_bind
  intro a state
  have hb := observe_bind (f a) (fun b => pure (k a b)) (fun b => PMF.pure (k a b))
    (fun b state => observe_pure (k a b) state) state
  rw [h a state] at hb
  exact hb

open scoped NNReal
open RetainedGridState IntegerAdaptiveExecution RetainedSampledExecution
variable {n L : ℕ} {G : Digraph (Fin n)} {D : Finset (Pair n)}
variable {selector : FlexibleCandidateSchedule.FamilyProvider G D (L : ℝ≥0) → Prop}
variable {H : ∃ P, selector P}

/-- The full graph-level result/log law is obtained by induction through the
actual controller, allowing arbitrary correlation with the physical ledger. -/
theorem execute_observe
    (sample : (a : PairFlags n) → StateT S PMF (RetainedTapeInput.Tape L a))
    (law : (a : PairFlags n) → PMF (RetainedTapeInput.Tape L a))
    (hsample : ∀ a state, observe (sample a) state = law a)
    (Q : Optimizer H) (hL : 0<L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (c : Cache H) (state : S) :
    observe (executeSampled sample Q hL C R restartFuel epochs c) state =
      executeSampled law Q hL C R restartFuel epochs c := by
  induction epochs generalizing c state with
  | zero => exact observe_pure _ _
  | succ epochs ih =>
      simp only [executeSampled]
      split_ifs with hz
      · exact observe_pure _ _
      · let a := stabilize Q R restartFuel c
        let inp := fun t => RetainedTapeInput.materialize hL a.cache.state.data.remaining t
        let scanned := fun t => scan Q hL C R a.cache.state.data.current
          (inp t).cell (inp t).order a.cache
        have next (t) (s : S) :
            observe (executeSampled sample Q hL C R restartFuel epochs (scanned t).cache) s =
              executeSampled law Q hL C R restartFuel epochs (scanned t).cache := ih _ _
        rw [observe_bind_map _ _ _ _ next,hsample]
        rfl


/-- The initial graph setup is deterministic; the physical entering state is
retained through the same once-only controller call. -/
theorem run_observe
    (sample : (a : PairFlags n) → StateT S PMF (RetainedTapeInput.Tape L a))
    (law : (a : PairFlags n) → PMF (RetainedTapeInput.Tape L a))
    (hsample : ∀ a state, observe (sample a) state = law a)
    (Q : Optimizer H) (hL : 0<L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (source : Code G D L) (state : S) :
    observe (runSampled sample Q hL C R restartFuel epochs source) state =
      runSampled law Q hL C R restartFuel epochs source := by
  simp only [runSampled]
  rw [observe_bind _ _ _ (fun b state => observe_pure _ state),
    execute_observe sample law hsample]
  rfl

end
end DirectedFlowCutGap.StatefulSamplerProjection
