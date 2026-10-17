import LightEFTSpanners.StoredCanonicalHostsBound

namespace LightEFTSpanners.StoredDiscoveredHosts
open Controller
inductive State where
  | components : StoredCanonicalEnumeration.State → State
  | hosts : StoredCanonicalHosts.State → State
  | halt : List StoredCanonicalHosts.Record → State
  deriving DecidableEq, Repr

def transition (n : ℕ) (edges : List StoredEdges.Edge) : State → Option State
  | .components (.halt rs) => some (.hosts (.records rs []))
  | .components s => (StoredCanonicalEnumeration.transition n edges s).map State.components
  | .hosts (.halt rs) => some (.halt rs)
  | .hosts s => (StoredCanonicalHosts.transition edges s).map State.hosts
  | .halt _ => none

def value {n : ℕ} (edges : List (Fin n × Fin n)) : List StoredCanonicalHosts.Record :=
  StoredCanonicalHosts.value (StoredEdges.encode edges) (StoredCanonicalEnumeration.records edges)

def bound (n m : ℕ) : ℕ := StoredCanonicalEnumeration.bound n m+
  StoredCanonicalHosts.bound n m n+2

def execute (n : ℕ) (edges : List StoredEdges.Edge) : List StoredCanonicalHosts.Record :=
  match Controller.run (transition n edges) (bound n edges.length) (.components (.range n [])) with
  | .halt rs => rs
  | _ => []

theorem components_lift (n : ℕ) (edges : List StoredEdges.Edge) {k : ℕ}
    {s t : StoredCanonicalEnumeration.State} (h : Trace (StoredCanonicalEnumeration.transition n edges) k s t) :
    Trace (transition n edges) k (.components s) (.components t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt out => simp [StoredCanonicalEnumeration.transition] at he
    | range a b => simpa only [transition,Option.map_some] using congrArg (Option.map State.components) he
    | roots a b => simpa only [transition,Option.map_some] using congrArg (Option.map State.components) he
    | root a b c d => simpa only [transition,Option.map_some] using congrArg (Option.map State.components) he
    | reverse a b => simpa only [transition,Option.map_some] using congrArg (Option.map State.components) he

theorem hosts_lift (n : ℕ) (edges : List StoredEdges.Edge) {k : ℕ}
    {s t : StoredCanonicalHosts.State} (h : Trace (StoredCanonicalHosts.transition edges) k s t) :
    Trace (transition n edges) k (.hosts s) (.hosts t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt out => simp [StoredCanonicalHosts.transition] at he
    | records a b => simpa only [transition,Option.map_some] using congrArg (Option.map State.hosts) he
    | filter a b c d => simpa only [transition,Option.map_some] using congrArg (Option.map State.hosts) he
    | reverse a b => simpa only [transition,Option.map_some] using congrArg (Option.map State.hosts) he
end LightEFTSpanners.StoredDiscoveredHosts
