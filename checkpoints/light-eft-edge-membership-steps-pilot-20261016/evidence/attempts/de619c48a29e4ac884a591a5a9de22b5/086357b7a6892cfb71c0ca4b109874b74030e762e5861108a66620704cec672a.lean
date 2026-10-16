import LightEFTSpanners.StoredVoteExecutable

/-! Draft successor: traverse literal eligible-host input records and run
all stored-draw voting transitions, counting the actual returned Booleans.
An external representation theorem must identify these records with the
intended distinct eligible hosts; no eligibility or cardinality is inferred. -/
namespace LightEFTSpanners.StoredHosts
open Controller
structure Input where
  edges : List StoredEdges.Edge
  draws : StoredVote.Draws
  deriving DecidableEq, Repr
inductive State where
  | hosts : List Input → ℕ → State
  | call : Input → List Input → ℕ → StoredVote.State → State
  | halt : Bool → State
  deriving DecidableEq, Repr

def transition (Q E : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n u v h : ℕ) (budget : ℚ) : State → Option State
  | .hosts [] count => some (.halt (decide (h≤count)))
  | .hosts (R::rs) count => some (.call R rs count (.draws R.draws []))
  | .call _ rs count (.halt b) => some (.hosts rs (count+(if b then 1 else 0)))
  | .call R rs count s =>
      (StoredVote.transition Q E R.edges W n u v budget s).map (State.call R rs count)
  | .halt _ => none

theorem call_lift (Q E : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n u v h : ℕ) (budget : ℚ) (R : Input) (rs : List Input) (count : ℕ)
    {k : ℕ} {s t : StoredVote.State}
    (ht : Trace (StoredVote.transition Q E R.edges W n u v budget) k s t) :
    Trace (transition Q E W n u v h budget) k (.call R rs count s) (.call R rs count t) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s t z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt b => simp [StoredVote.transition] at he
    | draws _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.call R rs count)) he
    | build _ _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.call R rs count)) he
    | reverse _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.call R rs count)) he
    | vote _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.call R rs count)) he

def successes (vote : Input → Bool) : List Input → ℕ
  | [] => 0
  | R::rs => (if vote R then 1 else 0)+successes vote rs

def bound (B : Input → ℕ) (rs : List Input) : ℕ := (rs.map fun R => B R+2).sum+1
end LightEFTSpanners.StoredHosts
