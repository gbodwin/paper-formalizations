import LightEFTSpanners.StoredFlagSampleExecutable

namespace LightEFTSpanners.StoredFlagBatch
open Controller
abbrev Input := List StoredFlagSample.Input
abbrev Output := List (List StoredEdges.Edge)
inductive State where
  | next : Input → Output → State
  | sample : Input → Output → StoredFlagSample.State → State
  | reverse : Output → Output → State
  | halt : Output → State
  deriving DecidableEq, Repr

def transition : State → Option State
  | .next [] acc => some (.reverse acc [])
  | .next (xs::rest) acc => some (.sample rest acc (.scan xs []))
  | .sample rest acc (.halt es) => some (.next rest (es::acc))
  | .sample rest acc s => (StoredFlagSample.transition s).map (.sample rest acc)
  | .reverse [] acc => some (.halt acc)
  | .reverse (x::xs) acc => some (.reverse xs (x::acc))
  | .halt _ => none

def value (xs : Input) : Output := xs.map StoredFlagSample.value
def budget (xs : Input) : ℕ := (xs.map fun x => StoredFlagSample.bound x+3).sum+2

theorem sample_lift {k : ℕ} {s t : StoredFlagSample.State}
    (h : Trace StoredFlagSample.transition k s t) (rest : Input) (acc : Output) :
    Trace transition k (.sample rest acc s) (.sample rest acc t) := by
  induction h with
  | refl => exact .refl _
  | @cons n s t u hs _ ih =>
    apply Trace.cons (t:=.sample rest acc t) ?_ ih
    cases s <;> simp_all [transition,StoredFlagSample.transition]

theorem reverse_trace (xs acc : Output) :
    Trace transition (xs.length+1) (.reverse xs acc) (.halt (xs.reverse++acc)) := by
  induction xs generalizing acc with
  | nil => exact Trace.one rfl
  | cons x xs ih =>
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
      Trace.cons (show transition (.reverse (x::xs) acc)=some (.reverse xs (x::acc)) from rfl) (ih (x::acc))
end LightEFTSpanners.StoredFlagBatch
