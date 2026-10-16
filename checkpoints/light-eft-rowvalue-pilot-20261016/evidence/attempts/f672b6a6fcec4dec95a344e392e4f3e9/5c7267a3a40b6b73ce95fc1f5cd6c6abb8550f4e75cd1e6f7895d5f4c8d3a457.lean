import LightEFTSpanners.StoredForestCandidateBound

namespace LightEFTSpanners.StoredForestCandidate
open Controller
inductive State where
  | inputs : StoredForestInput.State → State
  | candidate : StoredComponentCandidate.State → State
  | halt : StoredCandidates.Input → State
  deriving DecidableEq, Repr

def transition (n : ℕ) (bank : StoredDrawLookup.Bank) (e : StoredEdges.Edge)
    (W : StoredRecords.Weights) (t : ℚ) : State → Option State
  | .inputs (.halt rs) => some (.candidate (.catalogue ⟨e,rs⟩ (.inputs rs [])))
  | .inputs s => (StoredForestInput.transition n bank s).map State.inputs
  | .candidate (.candidate (.halt out)) => some (.halt out)
  | .candidate s => (StoredComponentCandidate.transition W t s).map State.candidate
  | .halt _ => none

def value {n : ℕ} (fs : List (List (Fin n × Fin n))) (bank : StoredDrawLookup.Bank)
    (e : StoredEdges.Edge) (W : StoredRecords.Weights) (t : ℚ) : StoredCandidates.Input :=
  StoredComponentCandidate.result W t ⟨e,StoredForestInput.value fs bank⟩

def bound (n : ℕ) (fs : List (List StoredEdges.Edge)) (bank : StoredDrawLookup.Bank)
    (e : StoredEdges.Edge) : ℕ := StoredForestInput.bound n fs bank+componentBound n (fs.length*n) e+2

def execute (n : ℕ) (fs : List (List StoredEdges.Edge)) (bank : StoredDrawLookup.Bank)
    (e : StoredEdges.Edge) (W : StoredRecords.Weights) (t : ℚ) : Option StoredCandidates.Input :=
  match Controller.run (transition n bank e W t) (bound n fs bank e)
      (.inputs (.forests (.forests 0 fs []))) with
  | .halt out => some out
  | _ => none

theorem inputs_lift (n : ℕ) (bank : StoredDrawLookup.Bank) (e : StoredEdges.Edge)
    (W : StoredRecords.Weights) (t : ℚ) {k : ℕ} {s u : StoredForestInput.State}
    (h : Trace (StoredForestInput.transition n bank) k s u) :
    Trace (transition n bank e W t) k (.inputs s) (.inputs u) := by
  induction h with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt out => simp [StoredForestInput.transition] at he
    | forests st => simpa only [transition,Option.map_some] using congrArg (Option.map State.inputs) he
    | attach st => simpa only [transition,Option.map_some] using congrArg (Option.map State.inputs) he

theorem candidate_lift (n : ℕ) (bank : StoredDrawLookup.Bank) (e : StoredEdges.Edge)
    (W : StoredRecords.Weights) (t : ℚ) {k : ℕ} {s u : StoredComponentCandidate.State}
    (h : Trace (StoredComponentCandidate.transition W t) k s u) :
    Trace (transition n bank e W t) k (.candidate s) (.candidate u) := by
  induction h with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | catalogue r st => simpa only [transition,Option.map_some] using congrArg (Option.map State.candidate) he
    | candidate st =>
      cases st with
      | halt out => simp [StoredComponentCandidate.transition,StoredCandidatePreparation.transition] at he
      | lookup a b => simpa only [transition,Option.map_some] using congrArg (Option.map State.candidate) he
      | hosts a b c => simpa only [transition,Option.map_some] using congrArg (Option.map State.candidate) he
end LightEFTSpanners.StoredForestCandidate
