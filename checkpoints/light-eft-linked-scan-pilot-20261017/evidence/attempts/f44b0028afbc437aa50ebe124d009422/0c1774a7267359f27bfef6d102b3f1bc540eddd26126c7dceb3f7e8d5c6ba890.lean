import LightEFTSpanners.StoredRecordExecutable
import LightEFTSpanners.SampleVoteExecutable

/-! Construct the whole sample-record list from literal stored edge draws,
then run the inherited vote controller on that very list. Each submachine
step and both list reversals are explicit transitions. -/
namespace LightEFTSpanners.StoredVote
open Controller
abbrev Draws := List (List StoredEdges.Edge)
def lists (Q E T S : List StoredEdges.Edge) : StoredSample.EdgeLists := ⟨Q,E,T,S⟩
def records (Q E T : List StoredEdges.Edge) (W : StoredRecords.Weights) (ss : Draws) :
    List SampleRecords.Records := ss.map fun S => StoredRecords.values (lists Q E T S) 0 W
inductive State where
  | draws : Draws → List SampleRecords.Records → State
  | build : List StoredEdges.Edge → Draws → List SampleRecords.Records → StoredRecords.State → State
  | reverse : List SampleRecords.Records → List SampleRecords.Records → State
  | vote : SampleVote.State → State
  | halt : Bool → State
  deriving DecidableEq, Repr

def transition (Q E T : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n u v : ℕ) (budget : ℚ) : State → Option State
  | .draws [] acc => some (.reverse acc [])
  | .draws (S::ss) acc => some (.build S ss acc (.row 0 W []))
  | .build _ ss acc (.halt R) => some (.draws ss (R::acc))
  | .build S ss acc s => (StoredRecords.transition (lists Q E T S) s).map (State.build S ss acc)
  | .reverse [] out => some (.vote (.samples out 0 0))
  | .reverse (R::rs) out => some (.reverse rs (R::out))
  | .vote (.halt b) => some (.halt b)
  | .vote s => (SampleVote.transition n u v budget s).map State.vote
  | .halt _ => none

theorem build_lift (Q E T S : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n u v : ℕ) (budget : ℚ) (ss : Draws) (acc : List SampleRecords.Records)
    {k : ℕ} {s t : StoredRecords.State} (h : Trace (StoredRecords.transition (lists Q E T S)) k s t) :
    Trace (transition Q E T W n u v budget) k (.build S ss acc s) (.build S ss acc t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt R => simp [StoredRecords.transition] at he
    | row _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.build S ss acc)) he
    | cell _ _ _ _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.build S ss acc)) he
    | entry _ _ _ _ _ _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.build S ss acc)) he
    | revRow _ _ _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.build S ss acc)) he
    | revMatrix _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.build S ss acc)) he

theorem vote_lift (Q E T : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n u v : ℕ) (budget : ℚ) {k : ℕ} {s t : SampleVote.State}
    (h : Trace (SampleVote.transition n u v budget) k s t) :
    Trace (transition Q E T W n u v budget) k (.vote s) (.vote t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt b => simp [SampleVote.transition] at he
    | samples _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map State.vote) he
    | materialize _ _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map State.vote) he
    | distance _ _ _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map State.vote) he
end LightEFTSpanners.StoredVote
