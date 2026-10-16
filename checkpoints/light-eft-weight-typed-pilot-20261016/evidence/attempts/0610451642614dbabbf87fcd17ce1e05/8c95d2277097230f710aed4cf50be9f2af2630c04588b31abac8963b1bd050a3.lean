import LightEFTSpanners.StoredVertexMembership

namespace LightEFTSpanners.StoredComponentHostFilter
open Controller
inductive State where
  | edges : List StoredEdges.Edge → List StoredEdges.Edge → State
  | left : StoredEdges.Edge → List StoredEdges.Edge → List StoredEdges.Edge → StoredVertexMembership.State → State
  | right : StoredEdges.Edge → List StoredEdges.Edge → List StoredEdges.Edge → StoredVertexMembership.State → State
  | reverse : List StoredEdges.Edge → List StoredEdges.Edge → State
  | halt : List StoredEdges.Edge → State
  deriving DecidableEq, Repr

def transition (vs : List ℕ) : State → Option State
  | .edges [] acc => some (.reverse acc [])
  | .edges (e::es) acc => if e.1=e.2 then some (.edges es acc)
      else some (.left e es acc (.scan e.1 vs))
  | .left _ es acc (.halt false) => some (.edges es acc)
  | .left e es acc (.halt true) => some (.right e es acc (.scan e.2 vs))
  | .left e es acc s => (StoredVertexMembership.transition s).map (State.left e es acc)
  | .right _ es acc (.halt false) => some (.edges es acc)
  | .right e es acc (.halt true) => some (.edges es (e::acc))
  | .right e es acc s => (StoredVertexMembership.transition s).map (State.right e es acc)
  | .reverse [] out => some (.halt out)
  | .reverse (e::es) out => some (.reverse es (e::out))
  | .halt _ => none

def selected (vs : List ℕ) (e : StoredEdges.Edge) : Bool :=
  decide (e.1≠e.2) && StoredVertexMembership.contains e.1 vs && StoredVertexMembership.contains e.2 vs

def edgeSteps (vs : List ℕ) (e : StoredEdges.Edge) : ℕ :=
  if e.1=e.2 then 1 else StoredVertexMembership.steps e.1 vs+2+
    if StoredVertexMembership.contains e.1 vs then StoredVertexMembership.steps e.2 vs+1 else 0

theorem left_lift (vs : List ℕ) (e : StoredEdges.Edge) (es acc : List StoredEdges.Edge)
    {k : ℕ} {s t : StoredVertexMembership.State} (h : Trace StoredVertexMembership.transition k s t) :
    Trace (transition vs) k (.left e es acc s) (.left e es acc t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt b => simp [StoredVertexMembership.transition] at he
    | scan v xs => simpa only [transition,Option.map_some] using congrArg (Option.map (State.left e es acc)) he

theorem right_lift (vs : List ℕ) (e : StoredEdges.Edge) (es acc : List StoredEdges.Edge)
    {k : ℕ} {s t : StoredVertexMembership.State} (h : Trace StoredVertexMembership.transition k s t) :
    Trace (transition vs) k (.right e es acc s) (.right e es acc t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt b => simp [StoredVertexMembership.transition] at he
    | scan v xs => simpa only [transition,Option.map_some] using congrArg (Option.map (State.right e es acc)) he

theorem edge_trace (vs : List ℕ) (e : StoredEdges.Edge) (es acc : List StoredEdges.Edge) :
    Trace (transition vs) (edgeSteps vs e) (.edges (e::es) acc)
      (.edges es (if selected vs e then e::acc else acc)) := by
  by_cases hd : e.1=e.2
  · simpa [edgeSteps,selected,hd] using Trace.one
      (show transition vs (.edges (e::es) acc)=some (.edges es acc) by simp [transition,hd])
  · have a := Trace.one (show transition vs (.edges (e::es) acc)=some (.left e es acc (.scan e.1 vs)) by simp [transition,hd])
    have b := left_lift vs e es acc (StoredVertexMembership.scan_trace e.1 vs)
    cases hl : StoredVertexMembership.contains e.1 vs with
    | false =>
      rw [hl] at b
      have c := Trace.one (show transition vs (.left e es acc (.halt false))=some (.edges es acc) from rfl)
      convert a.trans (b.trans c) using 1 <;> simp [edgeSteps,selected,hd,hl]
      omega
    | true =>
      rw [hl] at b
      have c := Trace.one (show transition vs (.left e es acc (.halt true))=some (.right e es acc (.scan e.2 vs)) from rfl)
      have d := right_lift vs e es acc (StoredVertexMembership.scan_trace e.2 vs)
      cases hr : StoredVertexMembership.contains e.2 vs with
      | false =>
        rw [hr] at d
        have f := Trace.one (show transition vs (.right e es acc (.halt false))=some (.edges es acc) from rfl)
        convert a.trans (b.trans (c.trans (d.trans f))) using 1 <;> simp [edgeSteps,selected,hd,hl,hr]
        omega
      | true =>
        rw [hr] at d
        have f := Trace.one (show transition vs (.right e es acc (.halt true))=some (.edges es (e::acc)) from rfl)
        convert a.trans (b.trans (c.trans (d.trans f))) using 1 <;> simp [edgeSteps,selected,hd,hl,hr]
        omega
end LightEFTSpanners.StoredComponentHostFilter
