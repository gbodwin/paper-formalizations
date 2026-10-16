import LightEFTSpanners.StoredWeightComparison

namespace LightEFTSpanners.StoredWeightMerge
open Controller
inductive State where
  | merge : List StoredEdges.Edge → List StoredEdges.Edge → List StoredEdges.Edge → State
  | compare : StoredEdges.Edge → List StoredEdges.Edge → StoredEdges.Edge → List StoredEdges.Edge → List StoredEdges.Edge → StoredWeightComparison.State → State
  | copy : List StoredEdges.Edge → List StoredEdges.Edge → State
  | reverse : List StoredEdges.Edge → List StoredEdges.Edge → State
  | halt : List StoredEdges.Edge → State
  deriving DecidableEq, Repr

def transition (bank : StoredOriginalWeightLookup.Bank) : State → Option State
  | .merge [] ys acc => some (.copy ys acc)
  | .merge xs [] acc => some (.copy xs acc)
  | .merge (x::xs) (y::ys) acc => some (.compare x xs y ys acc (.first (.scan bank)))
  | .compare x xs y ys acc (.halt b) => if b then some (.merge xs (y::ys) (x::acc)) else some (.merge (x::xs) ys (y::acc))
  | .compare x xs y ys acc st => (StoredWeightComparison.transition bank x y st).map (State.compare x xs y ys acc)
  | .copy [] acc => some (.reverse acc [])
  | .copy (x::xs) acc => some (.copy xs (x::acc))
  | .reverse [] out => some (.halt out)
  | .reverse (x::xs) out => some (.reverse xs (x::out))
  | .halt _ => none

theorem compare_lift (bank : StoredOriginalWeightLookup.Bank) (x y : StoredEdges.Edge)
    (xs ys acc : List StoredEdges.Edge) {k : ℕ} {s u : StoredWeightComparison.State}
    (ht : Trace (StoredWeightComparison.transition bank x y) k s u) :
    Trace (transition bank) k (.compare x xs y ys acc s) (.compare x xs y ys acc u) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s <;> try {simp [StoredWeightComparison.transition] at he}
    all_goals simpa only [transition,Option.map_some] using congrArg (Option.map (State.compare x xs y ys acc)) he

theorem reverse_trace (bank : StoredOriginalWeightLookup.Bank) (xs out : List StoredEdges.Edge) :
    Trace (transition bank) (xs.length+1) (.reverse xs out) (.halt (xs.reverse++out)) := by
  induction xs generalizing out with
  | nil => exact Trace.one rfl
  | cons x xs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm] using
      Trace.cons (show transition bank (.reverse (x::xs) out)=some (.reverse xs (x::out)) from rfl) (ih (x::out))

theorem copy_trace (bank : StoredOriginalWeightLookup.Bank) (xs acc : List StoredEdges.Edge) :
    Trace (transition bank) (xs.length+1) (.copy xs acc) (.reverse (xs.reverse++acc) []) := by
  induction xs generalizing acc with
  | nil => exact Trace.one rfl
  | cons x xs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm] using
      Trace.cons (show transition bank (.copy (x::xs) acc)=some (.copy xs (x::acc)) from rfl) (ih (x::acc))
end LightEFTSpanners.StoredWeightMerge
