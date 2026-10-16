import LightEFTSpanners.StoredComponentHostCorrect

namespace LightEFTSpanners.StoredCanonicalHosts
open Controller
abbrev Component := StoredCanonicalEnumeration.Record
abbrev Record := Component × List StoredEdges.Edge
inductive State where
  | records : List Component → List Record → State
  | filter : Component → List Component → List Record → StoredComponentHostFilter.State → State
  | reverse : List Record → List Record → State
  | halt : List Record → State
  deriving DecidableEq, Repr

def transition (edges : List StoredEdges.Edge) : State → Option State
  | .records [] acc => some (.reverse acc [])
  | .records (r::rs) acc => some (.filter r rs acc (.edges edges []))
  | .filter r rs acc (.halt es) => some (.records rs ((r,es)::acc))
  | .filter r rs acc s => (StoredComponentHostFilter.transition r.2 s).map (State.filter r rs acc)
  | .reverse [] out => some (.halt out)
  | .reverse (r::rs) out => some (.reverse rs (r::out))
  | .halt _ => none

def value (edges : List StoredEdges.Edge) (rs : List Component) : List Record :=
  rs.map fun r => (r,StoredComponentHostFilter.value r.2 edges)
def scanSteps (edges : List StoredEdges.Edge) : List Component → ℕ :=
  List.rec (motive := fun _ => ℕ) 1
    (fun r _ rest => StoredComponentHostFilter.steps r.2 edges+2+rest)

theorem scanSteps_nil (edges : List StoredEdges.Edge) : scanSteps edges [] = 1 := rfl

theorem scanSteps_cons (edges : List StoredEdges.Edge) (r : Component) (rs : List Component) :
    scanSteps edges (r::rs) = StoredComponentHostFilter.steps r.2 edges+2+scanSteps edges rs := rfl

theorem filter_lift (edges : List StoredEdges.Edge) (r : Component) (rs : List Component)
    (acc : List Record) {k : ℕ} {s t : StoredComponentHostFilter.State}
    (h : Trace (StoredComponentHostFilter.transition r.2) k s t) :
    Trace (transition edges) k (.filter r rs acc s) (.filter r rs acc t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt out => simp [StoredComponentHostFilter.transition] at he
    | edges es out => simpa only [transition,Option.map_some] using congrArg (Option.map (State.filter r rs acc)) he
    | left e es out st => simpa only [transition,Option.map_some] using congrArg (Option.map (State.filter r rs acc)) he
    | right e es out st => simpa only [transition,Option.map_some] using congrArg (Option.map (State.filter r rs acc)) he
    | reverse es out => simpa only [transition,Option.map_some] using congrArg (Option.map (State.filter r rs acc)) he

theorem scan_trace (edges : List StoredEdges.Edge) (rs : List Component) (acc : List Record) :
    Trace (transition edges) (scanSteps edges rs) (.records rs acc)
      (.reverse ((value edges rs).reverse++acc) []) := by
  induction rs generalizing acc with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    have a := Trace.one (show transition edges (.records (r::rs) acc)=
      some (.filter r rs acc (.edges edges [])) from rfl)
    have b := filter_lift edges r rs acc (StoredComponentHostFilter.filter_trace r.2 edges)
    have c := Trace.one (show transition edges (.filter r rs acc (.halt (StoredComponentHostFilter.value r.2 edges)))=
      some (.records rs ((r,StoredComponentHostFilter.value r.2 edges)::acc)) from rfl)
    have d := ih ((r,StoredComponentHostFilter.value r.2 edges)::acc)
    convert a.trans (b.trans (c.trans d)) using 1 <;>
      simp [scanSteps_cons,value,List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    omega

theorem reverse_trace (edges : List StoredEdges.Edge) (rs out : List Record) :
    Trace (transition edges) (rs.length+1) (.reverse rs out) (.halt (rs.reverse++out)) := by
  induction rs generalizing out with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc] using
      Trace.cons (show transition edges (.reverse (r::rs) out)=some (.reverse rs (r::out)) from rfl) (ih (r::out))

def steps (edges : List StoredEdges.Edge) (rs : List Component) : ℕ := scanSteps edges rs+rs.length+1

theorem hosts_trace (edges : List StoredEdges.Edge) (rs : List Component) :
    Trace (transition edges) (steps edges rs) (.records rs []) (.halt (value edges rs)) := by
  have a := scan_trace edges rs []
  simp only [List.append_nil] at a
  have b := reverse_trace edges (value edges rs).reverse []
  simpa [steps,value,Nat.add_assoc] using a.trans b
end LightEFTSpanners.StoredCanonicalHosts
