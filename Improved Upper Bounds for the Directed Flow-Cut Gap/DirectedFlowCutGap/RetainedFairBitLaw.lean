import DirectedFlowCutGap.RetainedDrawTrees

/-!
# Fair-bit law of actual retained adaptive execution

The finite draw-tree is produced by the existing single-pass controller.
Its ideal law is exactly the previously proved full LoggedResult law. The
bounded-bit lowering changes only the random adapter and retains a legal
output on every branch. Event comparisons concern the finite cut observable;
unbounded counters are not given a fictitious Fintype instance.
-/
namespace DirectedFlowCutGap.RetainedFairBitLaw
open scoped NNReal ENNReal BigOperators
open RetainedGridState IntegerAdaptiveExecution FiniteDrawTrees LazyFairBitTrees RetainedDrawTrees

variable {n L : ℕ} {G : Digraph (Fin n)} {D : Finset (Pair n)}
variable {selector : FlexibleCandidateSchedule.FamilyProvider G D (L : ℝ≥0) → Prop}
variable {H : ∃ P, selector P}

def cutTree (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (s : Code G D L) : FiniteDrawTrees.Tree (Finset (Fin n)) :=
  FiniteDrawTrees.map (fun d => cutSet d.result.cache.state.data.cut)
    (runTree Q hL C R restartFuel epochs s)

/-- This program invokes only fair bits, and consumes a bounded number of them. -/
def bitTree (T : ℕ) (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (s : Code G D L) : FiniteDrawTrees.Tree (Finset (Fin n)) :=
  lower T (cutTree Q hL C R restartFuel epochs s)

theorem bitTree_binary (T : ℕ) (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (s : Code G D L) :
    Binary (bitTree T Q hL C R restartFuel epochs s) := lower_binary T _

theorem bitTree_within (T : ℕ) (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (s : Code G D L) :
    Within ((epochs*(2*n*n))*T*sampleWidth n L)
      (bitTree T Q hL C R restartFuel epochs s) := by
  exact lower_within (within_map (runTree_within Q hL C R restartFuel epochs s) _)
    (widths_map (runTree_widths Q hL C R restartFuel epochs s) _) T

noncomputable section

private theorem ideal_bind {A B : Type} (p : FiniteDrawTrees.Tree A)
    (next : A → FiniteDrawTrees.Tree B) :
    ideal (FiniteDrawTrees.bind p next) = (ideal p).bind (fun a => ideal (next a)) :=
  law_bind uniformDraw p next

private theorem ideal_map {A B : Type} (f : A → B) (p : FiniteDrawTrees.Tree A) :
    ideal (FiniteDrawTrees.map f p) = (ideal p).map f := law_map uniformDraw f p

theorem executeTree_law (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel epochs : ℕ) (c : Cache H) :
    ideal (executeTree Q hL C R restartFuel epochs c) =
      RetainedSampledExecution.executeSampled RetainedExecutionLaw.sampleTape
        Q hL C R restartFuel epochs c := by
  induction epochs generalizing c with
  | zero => rfl
  | succ epochs ih =>
      simp only [executeTree, RetainedSampledExecution.executeSampled]
      split_ifs with hz
      · rfl
      · change ideal (FiniteDrawTrees.bind (sampleTape hL _) _) = _
        rw [ideal_bind, sampleTape_law]
        congr 1
        funext t
        change ideal (FiniteDrawTrees.bind _ _) = _
        rw [ideal_bind]
        simp only [executeTree] at ih
        rw [ih]
        rfl

theorem runTree_law (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel epochs : ℕ) (s : Code G D L) :
    ideal (runTree Q hL C R restartFuel epochs s) =
      RetainedExecutionLaw.sampledRunLaw Q hL C R restartFuel epochs s := by
  unfold runTree RetainedExecutionLaw.sampledRunLaw RetainedSampledExecution.runSampled
  change ideal (FiniteDrawTrees.bind _ _) = _
  rw [ideal_bind]
  rw [show ideal (RetainedSampledExecution.executeSampled (RetainedDrawTrees.sampleTape hL)
        Q hL C R restartFuel epochs _) = _ from
    executeTree_law Q hL C R restartFuel epochs _]
  rfl

/-- Exact identity to the already verified selected-provider output law. -/
theorem cutTree_law (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel epochs : ℕ) (s : Code G D L) :
    ideal (cutTree Q hL C R restartFuel epochs s) =
      RetainedExecutionLaw.outputLaw Q hL C R restartFuel epochs s := by
  rw [cutTree, ideal_map, runTree_law]
  exact RetainedExecutionLaw.sampledRunLaw_output Q hL C R restartFuel epochs s

/-- The error budget applies to the actual adaptive graph output, with its
state-dependent draw bounds and all possible restart/default branches. -/
theorem bit_event_le (T : ℕ) (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel epochs : ℕ) (s : Code G D L)
    (P : Finset (Fin n) → Prop) :
    FiniteAmplification.probability (ideal (bitTree T Q hL C R restartFuel epochs s)) P ≤
      FiniteAmplification.probability
        (RetainedExecutionLaw.outputLaw Q hL C R restartFuel epochs s) P +
          ((epochs*(2*n*n) : ℕ) : ℝ) * ((1 : ℝ)/2)^T := by
  have h := lowered_event_le
    (within_map (runTree_within Q hL C R restartFuel epochs s)
      (fun d => cutSet d.result.cache.state.data.cut)) T P
  change FiniteAmplification.probability (ideal (lower T (cutTree Q hL C R restartFuel epochs s))) P ≤
    FiniteAmplification.probability (ideal (cutTree Q hL C R restartFuel epochs s)) P + _ at h
  rw [cutTree_law] at h
  exact h

/-- Legal default values cannot create an invalid cut, even for zero trials. -/
theorem bit_valid (T : ℕ) (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel : ℕ) (hR : 1 < (R : ℝ≥0))
    (epochs : ℕ) (s : Code G D L)
    (hrestart : (interpret s).mass < (R : ℝ≥0)^restartFuel)
    (hepochs : (interpret s).mass < (R : ℝ≥0)^epochs)
    {X : Finset (Fin n)}
    (hX : X ∈ (ideal (bitTree T Q hL C R restartFuel epochs s)).support) :
    IsIntegralCut G X (D : Set (Pair n)) := by
  have hx := lowered_support_subset_ideal T (cutTree Q hL C R restartFuel epochs s) hX
  rw [cutTree_law] at hx
  exact RetainedExecutionLaw.output_valid Q hL C R restartFuel hR epochs s hrestart hepochs hx

end
end DirectedFlowCutGap.RetainedFairBitLaw
