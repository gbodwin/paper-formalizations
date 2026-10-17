import LightEFTSpanners.StoredHostRealAdmission

namespace LightEFTSpanners.StoredCandidates
open Controller
structure Input where
  edge : StoredEdges.Edge
  budget : ℚ
  hosts : List StoredHosts.Input
  deriving DecidableEq, Repr
inductive State where
  | candidates : List Input → List StoredEdges.Edge → State
  | call : Input → List Input → List StoredEdges.Edge → StoredHosts.State → State
  | halt : List StoredEdges.Edge → State
  deriving DecidableEq, Repr

def transition (Q : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n h : ℕ) : State → Option State
  | .candidates [] E => some (.halt E)
  | .candidates (R::rs) E => some (.call R rs E (.hosts R.hosts 0))
  | .call R rs E (.halt b) => some (.candidates rs (if b then R.edge::E else E))
  | .call R rs E s =>
      (StoredHosts.transition Q E W n R.edge.1 R.edge.2 h R.budget s).map
        (State.call R rs E)
  | .halt _ => none

theorem call_lift (Q : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n h : ℕ) (R : Input) (rs : List Input) (E : List StoredEdges.Edge)
    {k : ℕ} {s t : StoredHosts.State}
    (ht : Trace (StoredHosts.transition Q E W n R.edge.1 R.edge.2 h R.budget) k s t) :
    Trace (transition Q W n h) k (.call R rs E s) (.call R rs E t) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s t z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt b => simp [StoredHosts.transition] at he
    | hosts _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.call R rs E)) he
    | call _ _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.call R rs E)) he
end LightEFTSpanners.StoredCandidates
