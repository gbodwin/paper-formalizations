import LightEFTSpanners.StoredAssignmentExecutable

/-! Construct the eligible host records by actual short-circuit scans of a
stored incidence catalogue. Eligibility lists, host lists and draw lists are
input data; no eligible-host list or admission result is supplied. -/
namespace LightEFTSpanners.StoredHostPreparation
open Controller
structure Record where
  id : ℕ
  eligibleEdges : List StoredEdges.Edge
  host : StoredHosts.Input
  deriving DecidableEq, Repr
inductive State where
  | records : List Record → List Record → State
  | scan : Record → List Record → List Record → StoredEdges.State → State
  | reverse : List Record → List Record → State
  | halt : List Record → State
  deriving DecidableEq, Repr

def transition (e : StoredEdges.Edge) : State → Option State
  | .records [] acc => some (.reverse acc [])
  | .records (r::rs) acc => some (.scan r rs acc (.scan e r.eligibleEdges))
  | .scan r rs acc (.halt yes) => some (.records rs (if yes then r::acc else acc))
  | .scan r rs acc s => (StoredEdges.transition s).map (State.scan r rs acc)
  | .reverse [] out => some (.halt out)
  | .reverse (r::rs) out => some (.reverse rs (r::out))
  | .halt _ => none

def selected (e : StoredEdges.Edge) (rs : List Record) : List Record :=
  rs.filter fun r => StoredEdges.contains e r.eligibleEdges

def scanSteps (e : StoredEdges.Edge) : List Record → ℕ
  | [] => 1
  | r::rs => StoredEdges.steps e r.eligibleEdges+2+scanSteps e rs

theorem scan_lift (e : StoredEdges.Edge) (r : Record) (rs acc : List Record)
    {k : ℕ} {s t : StoredEdges.State} (ht : Trace StoredEdges.transition k s t) :
    Trace (transition e) k (.scan r rs acc s) (.scan r rs acc t) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s t z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt _ => simp [StoredEdges.transition] at he
    | scan _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.scan r rs acc)) he

theorem records_trace (e : StoredEdges.Edge) (rs acc : List Record) :
    Trace (transition e) (scanSteps e rs) (.records rs acc)
      (.reverse ((selected e rs).reverse++acc) []) := by
  induction rs generalizing acc with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    have start := Trace.one (show transition e (.records (r::rs) acc)=
      some (.scan r rs acc (.scan e r.eligibleEdges)) from rfl)
    have scanned := scan_lift e r rs acc (StoredEdges.scan_trace e r.eligibleEdges)
    have done := Trace.one (show transition e (.scan r rs acc (.halt (StoredEdges.contains e r.eligibleEdges)))=
      some (.records rs (if StoredEdges.contains e r.eligibleEdges then r::acc else acc)) from rfl)
    have rest := ih (if StoredEdges.contains e r.eligibleEdges then r::acc else acc)
    cases h : StoredEdges.contains e r.eligibleEdges <;>
      convert start.trans (scanned.trans (done.trans rest)) using 1 <;>
      simp [scanSteps,selected,h,List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

    all_goals omega

theorem reverse_trace (e : StoredEdges.Edge) (rs out : List Record) :
    Trace (transition e) (rs.length+1) (.reverse rs out) (.halt (rs.reverse++out)) := by
  induction rs generalizing out with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      Trace.cons (show transition e (.reverse (r::rs) out)=some (.reverse rs (r::out)) from rfl) (ih (r::out))

theorem prepare_trace (e : StoredEdges.Edge) (rs : List Record) :
    Trace (transition e) (scanSteps e rs+(selected e rs).length+1)
      (.records rs []) (.halt (selected e rs)) := by
  have first := records_trace e rs []
  simp only [List.append_nil] at first
  have h := first.trans (reverse_trace e (selected e rs).reverse [])
  simpa [Nat.add_assoc] using h
end LightEFTSpanners.StoredHostPreparation
