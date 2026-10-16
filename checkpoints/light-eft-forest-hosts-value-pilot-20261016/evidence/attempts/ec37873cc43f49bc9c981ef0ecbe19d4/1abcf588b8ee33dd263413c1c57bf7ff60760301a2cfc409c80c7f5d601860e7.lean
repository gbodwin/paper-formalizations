import LightEFTSpanners.StoredDiscoveredHostsCorrect

namespace LightEFTSpanners.StoredForestHosts
open Controller
abbrev Record := ℕ × StoredCanonicalHosts.Record
inductive State where
  | forests : ℕ → List (List StoredEdges.Edge) → List Record → State
  | discover : ℕ → List (List StoredEdges.Edge) → List Record → List StoredEdges.Edge → StoredDiscoveredHosts.State → State
  | append : ℕ → List (List StoredEdges.Edge) → List Record → List StoredCanonicalHosts.Record → State
  | reverse : List Record → List Record → State
  | halt : List Record → State
  deriving DecidableEq, Repr

def transition (n : ℕ) : State → Option State
  | .forests _ [] acc => some (.reverse acc [])
  | .forests i (es::fs) acc => some (.discover i fs acc es (.components (.range n [])))
  | .discover i fs acc _ (.halt rs) => some (.append i fs acc rs)
  | .discover i fs acc es s => (StoredDiscoveredHosts.transition n es s).map (State.discover i fs acc es)
  | .append i fs acc [] => some (.forests (i+1) fs acc)
  | .append i fs acc (r::rs) => some (.append i fs ((i,r)::acc) rs)
  | .reverse [] out => some (.halt out)
  | .reverse (r::rs) out => some (.reverse rs (r::out))
  | .halt _ => none

def value {n : ℕ} : ℕ → List (List (Fin n × Fin n)) → List Record :=
  fun i fs => List.rec (motive := fun _ => ℕ → List Record) (fun _ => [])
    (fun es _ next j => (StoredDiscoveredHosts.value es).map (fun r => (j,r)) ++ next (j+1)) fs i

theorem value_nil {n : ℕ} (i : ℕ) : value (n:=n) i [] = [] := rfl

theorem value_cons {n : ℕ} (i : ℕ) (es : List (Fin n × Fin n))
    (fs : List (List (Fin n × Fin n))) : value i (es::fs) =
    (StoredDiscoveredHosts.value es).map (fun r => (i,r)) ++ value (i+1) fs := rfl

theorem discover_lift (n i : ℕ) (fs : List (List StoredEdges.Edge)) (acc : List Record)
    (es : List StoredEdges.Edge) {k : ℕ} {s t : StoredDiscoveredHosts.State}
    (h : Trace (StoredDiscoveredHosts.transition n es) k s t) :
    Trace (transition n) k (.discover i fs acc es s) (.discover i fs acc es t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt out => simp [StoredDiscoveredHosts.transition] at he
    | components st => simpa only [transition,Option.map_some] using congrArg (Option.map (State.discover i fs acc es)) he
    | hosts st => simpa only [transition,Option.map_some] using congrArg (Option.map (State.discover i fs acc es)) he

theorem append_trace (n i : ℕ) (fs : List (List StoredEdges.Edge)) (acc : List Record)
    (rs : List StoredCanonicalHosts.Record) :
    Trace (transition n) (rs.length+1) (.append i fs acc rs)
      (.forests (i+1) fs ((rs.map (fun r => (i,r))).reverse++acc)) := by
  induction rs generalizing acc with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc] using
      Trace.cons (show transition n (.append i fs acc (r::rs))=some (.append i fs ((i,r)::acc) rs) from rfl)
        (ih ((i,r)::acc))
end LightEFTSpanners.StoredForestHosts
