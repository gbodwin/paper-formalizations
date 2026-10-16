import LightEFTSpanners.StoredComponentCandidateBound

namespace LightEFTSpanners.StoredComponentBank
open Controller
open StoredComponentCandidate (Input)
inductive State where
  | inputs : List Input → List StoredCandidates.Input → State
  | call : Input → List Input → List StoredCandidates.Input → StoredComponentCandidate.State → State
  | reverse : List StoredCandidates.Input → List StoredCandidates.Input → State
  | halt : List StoredCandidates.Input → State
  deriving DecidableEq, Repr

def transition (W : StoredRecords.Weights) (t : ℚ) : State → Option State
  | .inputs [] acc => some (.reverse acc [])
  | .inputs (r::rs) acc => some (.call r rs acc ((StoredComponentCandidate.State.catalogue r (.inputs r.components []))))
  | .call _ rs acc (.candidate (.halt out)) => some (.inputs rs (out::acc))
  | .call r rs acc s => (StoredComponentCandidate.transition W t s).map (State.call r rs acc)
  | .reverse [] out => some (.halt out)
  | .reverse (r::rs) out => some (.reverse rs (r::out))
  | .halt _ => none

def result (W : StoredRecords.Weights) (t : ℚ) (rs : List Input) : List StoredCandidates.Input :=
  rs.map (StoredComponentCandidate.result W t)
def scanSteps (W : StoredRecords.Weights) : List Input → ℕ
  | [] => 1
  | r::rs => StoredComponentCandidate.steps W r+2+scanSteps W rs

theorem call_lift (W : StoredRecords.Weights) (t : ℚ) (r : Input)
    (rs : List Input) (acc : List StoredCandidates.Input)
    {k : ℕ} {s u : StoredComponentCandidate.State}
    (ht : Trace (StoredComponentCandidate.transition W t) k s u) :
    Trace (transition W t) k (.call r rs acc s) (.call r rs acc u) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | catalogue _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.call r rs acc)) he
    | candidate u =>
      cases u with
      | halt _ => simp [StoredComponentCandidate.transition,StoredCandidatePreparation.transition] at he
      | lookup _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.call r rs acc)) he
      | hosts _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.call r rs acc)) he

theorem inputs_trace (W : StoredRecords.Weights) (t : ℚ) (rs : List Input)
    (acc : List StoredCandidates.Input) :
    Trace (transition W t) (scanSteps W rs) (.inputs rs acc)
      (.reverse ((result W t rs).reverse++acc) []) := by
  induction rs generalizing acc with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    have a := Trace.one (show transition W t (.inputs (r::rs) acc)=
      some (.call r rs acc ((StoredComponentCandidate.State.catalogue r (.inputs r.components [])))) from rfl)
    have b := call_lift W t r rs acc (StoredComponentCandidate.candidate_trace W t r)
    have c := Trace.one (show transition W t (.call r rs acc (.candidate (.halt (StoredComponentCandidate.result W t r))))=
      some (.inputs rs (StoredComponentCandidate.result W t r::acc)) from rfl)
    convert a.trans (b.trans (c.trans (ih (StoredComponentCandidate.result W t r::acc)))) using 1 <;>
      simp [scanSteps,result,List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    omega

theorem reverse_trace (W : StoredRecords.Weights) (t : ℚ) (rs out : List StoredCandidates.Input) :
    Trace (transition W t) (rs.length+1) (.reverse rs out) (.halt (rs.reverse++out)) := by
  induction rs generalizing out with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      Trace.cons (show transition W t (.reverse (r::rs) out)=some (.reverse rs (r::out)) from rfl) (ih (r::out))

theorem bank_trace (W : StoredRecords.Weights) (t : ℚ) (rs : List Input) :
    Trace (transition W t) (scanSteps W rs+rs.length+1) (.inputs rs []) (.halt (result W t rs)) := by
  have a := inputs_trace W t rs []
  simp only [List.append_nil] at a
  have b := reverse_trace W t (result W t rs).reverse []
  simpa [result,Nat.add_assoc] using a.trans b

def inputBound (rs : List Input) : ℕ :=
  (rs.map fun r => StoredComponentCandidate.inputBound r+3).sum+2

theorem steps_le_input (W : StoredRecords.Weights) (rs : List Input) :
    scanSteps W rs+rs.length+1 ≤ inputBound rs := by
  induction rs with
  | nil => simp [scanSteps,inputBound]
  | cons r rs ih =>
    have a := StoredComponentCandidate.steps_le_input W r
    simp only [scanSteps,inputBound,List.map_cons,List.sum_cons,List.length_cons] at *
    omega
end LightEFTSpanners.StoredComponentBank
