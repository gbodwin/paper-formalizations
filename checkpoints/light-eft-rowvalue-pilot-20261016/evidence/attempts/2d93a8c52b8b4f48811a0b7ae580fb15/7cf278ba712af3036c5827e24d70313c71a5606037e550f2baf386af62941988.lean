import LightEFTSpanners.StoredComponentCatalogueEncoding

namespace LightEFTSpanners.StoredComponentCandidate
open Controller
structure Input where
  edge : StoredEdges.Edge
  components : List StoredComponentRecord.Input
  deriving DecidableEq, Repr
inductive State where
  | catalogue : Input → StoredComponentCatalogue.State → State
  | candidate : StoredCandidatePreparation.State → State
  deriving DecidableEq, Repr

def transition (W : StoredRecords.Weights) (t : ℚ) : State → Option State
  | .catalogue r (.halt out) => some (.candidate (StoredCandidatePreparation.start W ⟨r.edge,out⟩))
  | .catalogue r s => (StoredComponentCatalogue.transition s).map (State.catalogue r)
  | .candidate s => (StoredCandidatePreparation.transition W t s).map State.candidate

def prepared (r : Input) : StoredCandidatePreparation.Input :=
  ⟨r.edge,StoredComponentCatalogue.result r.components⟩
def result (W : StoredRecords.Weights) (t : ℚ) (r : Input) : StoredCandidates.Input :=
  StoredCandidatePreparation.result W t (prepared r)
def steps (W : StoredRecords.Weights) (r : Input) : ℕ :=
  StoredComponentCatalogue.scanSteps r.components+r.components.length+1+1+
    StoredCandidatePreparation.steps W (prepared r)

theorem catalogue_lift (W : StoredRecords.Weights) (t : ℚ) (r : Input)
    {k : ℕ} {s u : StoredComponentCatalogue.State}
    (ht : Trace StoredComponentCatalogue.transition k s u) :
    Trace (transition W t) k (.catalogue r s) (.catalogue r u) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt _ => simp [StoredComponentCatalogue.transition] at he
    | inputs _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.catalogue r)) he
    | call _ _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.catalogue r)) he
    | reverse _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.catalogue r)) he

theorem candidate_lift (W : StoredRecords.Weights) (t : ℚ)
    {k : ℕ} {s u : StoredCandidatePreparation.State}
    (ht : Trace (StoredCandidatePreparation.transition W t) k s u) :
    Trace (transition W t) k (.candidate s) (.candidate u) := by
  induction ht with
  | refl => exact .refl _
  | cons he _ ih =>
    exact Trace.cons (by simpa only [transition,Option.map_some] using congrArg (Option.map State.candidate) he) ih

theorem candidate_trace (W : StoredRecords.Weights) (t : ℚ) (r : Input) :
    Trace (transition W t) (steps W r) (.catalogue r (.inputs r.components []))
      (.candidate (.halt (result W t r))) := by
  have a := catalogue_lift W t r (StoredComponentCatalogue.bank_trace r.components)
  have b := Trace.one (show transition W t (.catalogue r (.halt (StoredComponentCatalogue.result r.components)))=
    some (.candidate (StoredCandidatePreparation.start W (prepared r))) from rfl)
  have c := candidate_lift W t (StoredCandidatePreparation.prepare_trace W t (prepared r))
  simpa only [steps,result,Nat.add_assoc] using a.trans (b.trans c)
end LightEFTSpanners.StoredComponentCandidate
