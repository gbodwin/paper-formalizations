import LightEFTSpanners.StoredComponentRecord

namespace LightEFTSpanners.StoredComponentCatalogue
open Controller
open StoredComponentRecord (Input)
inductive State where
  | inputs : List Input → List StoredHostPreparation.Record → State
  | call : Input → List Input → List StoredHostPreparation.Record → StoredComponentRecord.State → State
  | reverse : List StoredHostPreparation.Record → List StoredHostPreparation.Record → State
  | halt : List StoredHostPreparation.Record → State
  deriving DecidableEq, Repr

def transition : State → Option State
  | .inputs [] acc => some (.reverse acc [])
  | .inputs (r::rs) acc => some (.call r rs acc ((StoredComponentRecord.State.pairs r (.rows r.vertices r.vertices []))))
  | .call _ rs acc (.halt out) => some (.inputs rs (out::acc))
  | .call r rs acc s => (StoredComponentRecord.transition s).map (State.call r rs acc)
  | .reverse [] out => some (.halt out)
  | .reverse (r::rs) out => some (.reverse rs (r::out))
  | .halt _ => none

def result (rs : List Input) : List StoredHostPreparation.Record :=
  rs.map (StoredComponentRecord.result)
def scanSteps : List Input → ℕ
  | [] => 1
  | r::rs => StoredComponentRecord.steps r+2+scanSteps rs

theorem call_lift (r : Input)
    (rs : List Input) (acc : List StoredHostPreparation.Record)
    {k : ℕ} {s u : StoredComponentRecord.State}
    (ht : Trace (StoredComponentRecord.transition) k s u) :
    Trace (transition) k (.call r rs acc s) (.call r rs acc u) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt _ => simp [StoredComponentRecord.transition] at he
    | pairs _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.call r rs acc)) he

theorem inputs_trace (rs : List Input)
    (acc : List StoredHostPreparation.Record) :
    Trace (transition) (scanSteps rs) (.inputs rs acc)
      (.reverse ((result rs).reverse++acc) []) := by
  induction rs generalizing acc with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    have a := Trace.one (show transition (.inputs (r::rs) acc)=
      some (.call r rs acc ((StoredComponentRecord.State.pairs r (.rows r.vertices r.vertices [])))) from rfl)
    have b := call_lift r rs acc (StoredComponentRecord.record_trace r)
    have c := Trace.one (show transition (.call r rs acc (.halt (StoredComponentRecord.result r)))=
      some (.inputs rs (StoredComponentRecord.result r::acc)) from rfl)
    convert a.trans (b.trans (c.trans (ih (StoredComponentRecord.result r::acc)))) using 1 <;>
      simp [scanSteps,result,List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    omega

theorem reverse_trace (rs out : List StoredHostPreparation.Record) :
    Trace (transition) (rs.length+1) (.reverse rs out) (.halt (rs.reverse++out)) := by
  induction rs generalizing out with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      Trace.cons (show transition (.reverse (r::rs) out)=some (.reverse rs (r::out)) from rfl) (ih (r::out))

theorem bank_trace (rs : List Input) :
    Trace (transition) (scanSteps rs+rs.length+1) (.inputs rs []) (.halt (result rs)) := by
  have a := inputs_trace rs []
  simp only [List.append_nil] at a
  have b := reverse_trace (result rs).reverse []
  simpa [result,Nat.add_assoc] using a.trans b

def inputBound (rs : List Input) : ℕ :=
  (rs.map fun r => StoredComponentRecord.steps r+3).sum+2

theorem steps_le_input (rs : List Input) :
    scanSteps rs+rs.length+1 ≤ inputBound rs := by
  induction rs with
  | nil => simp [scanSteps,inputBound]
  | cons r rs ih =>
    simp only [scanSteps,inputBound,List.map_cons,List.sum_cons,List.length_cons] at *
    omega
end LightEFTSpanners.StoredComponentCatalogue
