import LightEFTSpanners.StoredOriginalCallerBudget

namespace LightEFTSpanners.StoredOriginalGraphCaller
open Controller
inductive State where
  | prepare : StoredSortedCandidateInput.State → State
  | run : List StoredForestBank.Input → StoredWeightedForestCandidates.State → State
  deriving DecidableEq, Repr

def transition (n h : ℕ) (fs : List (List StoredEdges.Edge)) (Q E : List StoredEdges.Edge)
    (weights : StoredOriginalWeightLookup.Bank) (bank : StoredCandidateDrawLookup.Bank) (t : ℚ) : State → Option State
  | .prepare (.records (.halt rs)) => some (.run rs (.weights (.rows 0 n [])))
  | .prepare st => (StoredSortedCandidateInput.transition weights Q bank st).map State.prepare
  | .run rs st => (StoredWeightedForestCandidates.transition n h fs Q E weights t rs st).map (State.run rs)

def bound (n : ℕ) (fs : List (List StoredEdges.Edge)) (Q E xs : List StoredEdges.Edge)
    (weights : StoredOriginalWeightLookup.Bank) (bank : StoredCandidateDrawLookup.Bank) : ℕ :=
  StoredSortedCandidateInput.bound weights Q bank xs+1+StoredOriginalWeightMatrix.bound n weights.length+1+
    StoredSortedCandidateInput.callerBound n fs Q E xs bank

theorem prepare_lift (n h : ℕ) (fs : List (List StoredEdges.Edge)) (Q E : List StoredEdges.Edge)
    (weights : StoredOriginalWeightLookup.Bank) (bank : StoredCandidateDrawLookup.Bank) (t : ℚ)
    {k : ℕ} {s u : StoredSortedCandidateInput.State} (ht : Trace (StoredSortedCandidateInput.transition weights Q bank) k s u) :
    Trace (transition n h fs Q E weights bank t) k (.prepare s) (.prepare u) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | sorting st => simpa only [transition,StoredSortedCandidateInput.transition,Option.map_some] using congrArg (Option.map State.prepare) he
    | records st =>
      cases st <;> try {simp [StoredSortedCandidateInput.transition,StoredOriginalCandidateRecords.transition] at he}
      all_goals simpa only [transition,Option.map_some] using congrArg (Option.map State.prepare) he

theorem run_lift (n h : ℕ) (fs : List (List StoredEdges.Edge)) (Q E : List StoredEdges.Edge)
    (weights : StoredOriginalWeightLookup.Bank) (bank : StoredCandidateDrawLookup.Bank) (t : ℚ)
    (rs : List StoredForestBank.Input) {k : ℕ} {s u : StoredWeightedForestCandidates.State}
    (ht : Trace (StoredWeightedForestCandidates.transition n h fs Q E weights t rs) k s u) :
    Trace (transition n h fs Q E weights bank t) k (.run rs s) (.run rs u) := by
  induction ht with
  | refl => exact .refl _
  | cons he _ ih =>
    exact Trace.cons (by simpa only [transition,Option.map_some] using congrArg (Option.map (State.run rs)) he) ih
end LightEFTSpanners.StoredOriginalGraphCaller
