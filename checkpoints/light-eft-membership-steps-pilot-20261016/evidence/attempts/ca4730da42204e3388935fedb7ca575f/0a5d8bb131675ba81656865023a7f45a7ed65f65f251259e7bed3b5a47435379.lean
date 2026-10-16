import LightEFTSpanners.StoredCandidateDrawLookup

namespace LightEFTSpanners.StoredOriginalCandidateRecords
open Controller
inductive State where
  | scan : List StoredEdges.Edge → List StoredForestBank.Input → State
  | member : StoredEdges.Edge → List StoredEdges.Edge → List StoredForestBank.Input → StoredEdges.State → State
  | draws : StoredEdges.Edge → List StoredEdges.Edge → List StoredForestBank.Input → StoredCandidateDrawLookup.State → State
  | halt : List StoredForestBank.Input → State
  deriving DecidableEq, Repr

def transition (Q : List StoredEdges.Edge) (bank : StoredCandidateDrawLookup.Bank) : State → Option State
  | .scan [] acc => some (.halt acc)
  | .scan (x::xs) acc => some (.member x xs acc (.scan x Q))
  | .member _ xs acc (.halt true) => some (.scan xs acc)
  | .member x xs acc (.halt false) => some (.draws x xs acc (.scan bank))
  | .member x xs acc st => StoredEdges.transition st |>.map (State.member x xs acc)
  | .draws x xs acc (.halt ds) => some (.scan xs (⟨x,ds⟩::acc))
  | .draws x xs acc st => (StoredCandidateDrawLookup.transition x st).map (State.draws x xs acc)
  | .halt _ => none

def value (Q : List StoredEdges.Edge) (bank : StoredCandidateDrawLookup.Bank) :
    List StoredEdges.Edge → List StoredForestBank.Input :=
  List.rec (motive := fun _ => List StoredForestBank.Input) []
    (fun x _ rest => if StoredEdges.contains x Q then rest
      else ⟨x,StoredCandidateDrawLookup.value x bank⟩::rest)

theorem value_nil (Q : List StoredEdges.Edge) (bank : StoredCandidateDrawLookup.Bank) :
    value Q bank [] = [] := rfl

theorem value_cons (Q : List StoredEdges.Edge) (bank : StoredCandidateDrawLookup.Bank)
    (x : StoredEdges.Edge) (xs : List StoredEdges.Edge) :
    value Q bank (x::xs) = if StoredEdges.contains x Q then value Q bank xs
      else ⟨x,StoredCandidateDrawLookup.value x bank⟩::value Q bank xs := rfl


def bound (Q : List StoredEdges.Edge) (bank : StoredCandidateDrawLookup.Bank) (xs : List StoredEdges.Edge) : ℕ :=
  xs.length*(Q.length+bank.length+5)+1

theorem member_lift (Q : List StoredEdges.Edge) (bank : StoredCandidateDrawLookup.Bank)
    (x : StoredEdges.Edge) (xs : List StoredEdges.Edge) (acc : List StoredForestBank.Input)
    {k : ℕ} {s u : StoredEdges.State} (ht : Trace StoredEdges.transition k s u) :
    Trace (transition Q bank) k (.member x xs acc s) (.member x xs acc u) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt b => simp [StoredEdges.transition] at he
    | scan e es => simpa only [transition,Option.map_some] using congrArg (Option.map (State.member x xs acc)) he

theorem draws_lift (Q : List StoredEdges.Edge) (bank : StoredCandidateDrawLookup.Bank)
    (x : StoredEdges.Edge) (xs : List StoredEdges.Edge) (acc : List StoredForestBank.Input)
    {k : ℕ} {s u : StoredCandidateDrawLookup.State} (ht : Trace (StoredCandidateDrawLookup.transition x) k s u) :
    Trace (transition Q bank) k (.draws x xs acc s) (.draws x xs acc u) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt ds => simp [StoredCandidateDrawLookup.transition] at he
    | scan rs => simpa only [transition,Option.map_some] using congrArg (Option.map (State.draws x xs acc)) he
end LightEFTSpanners.StoredOriginalCandidateRecords
