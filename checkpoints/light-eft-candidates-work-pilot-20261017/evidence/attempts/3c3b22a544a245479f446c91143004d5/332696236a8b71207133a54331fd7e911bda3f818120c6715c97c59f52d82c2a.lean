import LightEFTSpanners.StoredOriginalWeightMatrixEncoding

namespace LightEFTSpanners.StoredWeightedForestCandidates
open Controller
inductive State where
  | weights : StoredOriginalWeightMatrix.State → State
  | candidates : StoredRecords.Weights → StoredForestCandidates.State → State
  deriving DecidableEq, Repr

def transition (n h : ℕ) (fs : List (List StoredEdges.Edge)) (Q E : List StoredEdges.Edge)
    (bank : StoredOriginalWeightLookup.Bank) (t : ℚ) (rs : List StoredForestBank.Input) : State → Option State
  | .weights (.halt W) => some (.candidates W (.prepare (.inputs rs [])))
  | .weights s => (StoredOriginalWeightMatrix.transition n bank s).map State.weights
  | .candidates W s => (StoredForestCandidates.transition fs Q E W n h t s).map (State.candidates W)

def bound (n : ℕ) (fs : List (List StoredEdges.Edge)) (Q E : List StoredEdges.Edge)
    (bank : StoredOriginalWeightLookup.Bank) (rs : List StoredForestBank.Input) : ℕ :=
  StoredOriginalWeightMatrix.bound n bank.length+1+StoredForestCandidates.bound n fs Q E rs

def execute (n h : ℕ) (fs : List (List StoredEdges.Edge)) (Q E : List StoredEdges.Edge)
    (bank : StoredOriginalWeightLookup.Bank) (t : ℚ) (rs : List StoredForestBank.Input) : List StoredEdges.Edge :=
  match Controller.run (transition n h fs Q E bank t rs) (bound n fs Q E bank rs) (.weights (.rows 0 n [])) with
  | .candidates _ (.select (.halt out)) => out
  | _ => E

theorem weights_lift (n h : ℕ) (fs : List (List StoredEdges.Edge)) (Q E : List StoredEdges.Edge)
    (bank : StoredOriginalWeightLookup.Bank) (t : ℚ) (rs : List StoredForestBank.Input)
    {k : ℕ} {s u : StoredOriginalWeightMatrix.State} (ht : Trace (StoredOriginalWeightMatrix.transition n bank) k s u) :
    Trace (transition n h fs Q E bank t rs) k (.weights s) (.weights u) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s <;> try {simp [StoredOriginalWeightMatrix.transition] at he}
    all_goals simpa only [transition,Option.map_some] using congrArg (Option.map State.weights) he

theorem candidates_lift (n h : ℕ) (fs : List (List StoredEdges.Edge)) (Q E : List StoredEdges.Edge)
    (bank : StoredOriginalWeightLookup.Bank) (t : ℚ) (rs : List StoredForestBank.Input) (W : StoredRecords.Weights)
    {k : ℕ} {s u : StoredForestCandidates.State} (ht : Trace (StoredForestCandidates.transition fs Q E W n h t) k s u) :
    Trace (transition n h fs Q E bank t rs) k (.candidates W s) (.candidates W u) := by
  induction ht with
  | refl => exact .refl _
  | cons he _ ih =>
    exact Trace.cons
      (by simpa only [transition,Option.map_some] using congrArg (Option.map (State.candidates W)) he) ih
end LightEFTSpanners.StoredWeightedForestCandidates
