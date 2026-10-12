import LightEFTSpanners.StoredWeightLookup

namespace LightEFTSpanners.StoredCandidatePreparation
open Controller
structure Input where
  edge : StoredEdges.Edge
  catalogue : List StoredHostPreparation.Record
  deriving DecidableEq, Repr
inductive State where
  | lookup : Input → StoredWeightLookup.State → State
  | hosts : Input → ℚ → StoredPreparedHostRecords.State → State
  | halt : StoredCandidates.Input → State
  deriving DecidableEq, Repr

def transition (_W : StoredRecords.Weights) (t : ℚ) : State → Option State
  | .lookup r (.halt w) => some (.hosts r (t*w) (.prepare (.records r.catalogue [])))
  | .lookup r s => (StoredWeightLookup.transition s).map (State.lookup r)
  | .hosts r budget (.halt hs) => some (.halt ⟨r.edge,budget,hs⟩)
  | .hosts r budget s => (StoredPreparedHostRecords.transition r.edge s).map (State.hosts r budget)
  | .halt _ => none

def start (W : StoredRecords.Weights) (r : Input) : State :=
  .lookup r (.rows r.edge.1 r.edge.2 W)
def result (W : StoredRecords.Weights) (t : ℚ) (r : Input) : StoredCandidates.Input :=
  ⟨r.edge,t*StoredWeightLookup.value r.edge.1 r.edge.2 W,
    StoredPreparedHostRecords.result r.edge r.catalogue⟩

theorem lookup_lift (W : StoredRecords.Weights) (t : ℚ) (r : Input)
    {k : ℕ} {s u : StoredWeightLookup.State} (h : Trace StoredWeightLookup.transition k s u) :
    Trace (transition W t) k (.lookup r s) (.lookup r u) := by
  induction h with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt _ => simp [StoredWeightLookup.transition] at he
    | rows _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.lookup r)) he
    | cells _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.lookup r)) he

theorem hosts_lift (W : StoredRecords.Weights) (t : ℚ) (r : Input) (budget : ℚ)
    {k : ℕ} {s u : StoredPreparedHostRecords.State}
    (h : Trace (StoredPreparedHostRecords.transition r.edge) k s u) :
    Trace (transition W t) k (.hosts r budget s) (.hosts r budget u) := by
  induction h with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt _ => simp [StoredPreparedHostRecords.transition] at he
    | prepare _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.hosts r budget)) he
    | copy _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.hosts r budget)) he
    | reverse _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.hosts r budget)) he

def steps (W : StoredRecords.Weights) (r : Input) : ℕ :=
  StoredWeightLookup.steps r.edge.1 r.edge.2 W+
    StoredHostPreparation.scanSteps r.edge r.catalogue+
      3*(StoredHostPreparation.selected r.edge r.catalogue).length+6

theorem prepare_trace (W : StoredRecords.Weights) (t : ℚ) (r : Input) :
    Trace (transition W t) (steps W r) (start W r) (.halt (result W t r)) := by
  have first := lookup_lift W t r (StoredWeightLookup.lookup_trace r.edge.1 r.edge.2 W)
  have next := Trace.one (show transition W t (.lookup r (.halt (StoredWeightLookup.value r.edge.1 r.edge.2 W)))=
    some (.hosts r (t*StoredWeightLookup.value r.edge.1 r.edge.2 W) (.prepare (.records r.catalogue []))) from rfl)
  have middle := hosts_lift W t r (t*StoredWeightLookup.value r.edge.1 r.edge.2 W)
    (StoredPreparedHostRecords.records_trace r.edge r.catalogue)
  have last := Trace.one (show transition W t
    (.hosts r (t*StoredWeightLookup.value r.edge.1 r.edge.2 W)
      (.halt (StoredPreparedHostRecords.result r.edge r.catalogue)))=some (.halt (result W t r)) from rfl)
  convert first.trans (next.trans (middle.trans last)) using 1 <;> simp [steps,start]
  omega

def inputBound (r : Input) : ℕ :=
  r.edge.1+r.edge.2+2+StoredPreparedHostRecords.inputBound r.catalogue+2

theorem steps_le (W : StoredRecords.Weights) (r : Input) : steps W r ≤ inputBound r := by
  have a := StoredWeightLookup.steps_le r.edge.1 r.edge.2 W
  have b := StoredPreparedHostRecords.steps_le_input r.edge r.catalogue
  unfold steps inputBound
  omega
end LightEFTSpanners.StoredCandidatePreparation
