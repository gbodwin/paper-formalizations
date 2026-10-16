import LightEFTSpanners.StoredSortSplitExecutable

namespace LightEFTSpanners.StoredWeightSort
open Controller
inductive Frame where
  | right : List StoredEdges.Edge → Frame
  | merge : List StoredEdges.Edge → Frame
  deriving DecidableEq, Repr
inductive State where
  | sort : List StoredEdges.Edge → List Frame → State
  | split : List StoredEdges.Edge → List Frame → StoredSortSplit.State → State
  | merging : List Frame → StoredWeightMerge.State → State
  | returning : List StoredEdges.Edge → List Frame → State
  | halt : List StoredEdges.Edge → State
  deriving DecidableEq, Repr

def transition (bank : StoredOriginalWeightLookup.Bank) : State → Option State
  | .sort [] stack => some (.returning [] stack)
  | .sort [x] stack => some (.returning [x] stack)
  | .sort (x::y::xs) stack => some (.split (x::y::xs) stack (.count (x::y::xs) 0))
  | .split _ stack (.halt left right) => some (.sort left (.right right::stack))
  | .split xs stack st => (StoredSortSplit.transition xs st).map (State.split xs stack)
  | .returning out [] => some (.halt out)
  | .returning left (.right right::stack) => some (.sort right (.merge left::stack))
  | .returning right (.merge left::stack) => some (.merging stack (.merge left right []))
  | .merging stack (.halt out) => some (.returning out stack)
  | .merging stack st => (StoredWeightMerge.transition bank st).map (State.merging stack)
  | .halt _ => none

theorem split_lift (bank : StoredOriginalWeightLookup.Bank) (xs : List StoredEdges.Edge) (stack : List Frame)
    {k : ℕ} {s u : StoredSortSplit.State} (ht : Trace (StoredSortSplit.transition xs) k s u) :
    Trace (transition bank) k (.split xs stack s) (.split xs stack u) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s <;> try {simp [StoredSortSplit.transition] at he}
    all_goals simpa only [transition,Option.map_some] using congrArg (Option.map (State.split xs stack)) he

theorem merge_lift (bank : StoredOriginalWeightLookup.Bank) (stack : List Frame)
    {k : ℕ} {s u : StoredWeightMerge.State} (ht : Trace (StoredWeightMerge.transition bank) k s u) :
    Trace (transition bank) k (.merging stack s) (.merging stack u) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s <;> try {simp [StoredWeightMerge.transition] at he}
    all_goals simpa only [transition,Option.map_some] using congrArg (Option.map (State.merging stack)) he
end LightEFTSpanners.StoredWeightSort
