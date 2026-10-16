import LightEFTSpanners.StoredHostPreparationEncoding

namespace LightEFTSpanners.StoredPreparedHostRecords
open Controller
open StoredHostPreparation (Record)
inductive State where
  | prepare : StoredHostPreparation.State → State
  | copy : List Record → List StoredHosts.Input → State
  | reverse : List StoredHosts.Input → List StoredHosts.Input → State
  | halt : List StoredHosts.Input → State
  deriving DecidableEq, Repr

def transition (e : StoredEdges.Edge) : State → Option State
  | .prepare (.halt rs) => some (.copy rs [])
  | .prepare s => (StoredHostPreparation.transition e s).map State.prepare
  | .copy [] acc => some (.reverse acc [])
  | .copy (r::rs) acc => some (.copy rs (r.host::acc))
  | .reverse [] out => some (.halt out)
  | .reverse (h::hs) out => some (.reverse hs (h::out))
  | .halt _ => none

theorem prepare_lift (e : StoredEdges.Edge) {k : ℕ} {s t : StoredHostPreparation.State}
    (h : Trace (StoredHostPreparation.transition e) k s t) :
    Trace (transition e) k (.prepare s) (.prepare t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt _ => simp [StoredHostPreparation.transition] at he
    | records _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map State.prepare) he
    | scan _ _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map State.prepare) he
    | reverse _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map State.prepare) he

theorem copy_trace (e : StoredEdges.Edge) (rs : List Record) (acc : List StoredHosts.Input) :
    Trace (transition e) (rs.length+1) (.copy rs acc)
      (.reverse ((rs.map Record.host).reverse++acc) []) := by
  induction rs generalizing acc with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      Trace.cons (show transition e (.copy (r::rs) acc)=some (.copy rs (r.host::acc)) from rfl) (ih (r.host::acc))

theorem reverse_trace (e : StoredEdges.Edge) (rs acc : List StoredHosts.Input) :
    Trace (transition e) (rs.length+1) (.reverse rs acc) (.halt (rs.reverse++acc)) := by
  induction rs generalizing acc with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      Trace.cons (show transition e (.reverse (r::rs) acc)=some (.reverse rs (r::acc)) from rfl) (ih (r::acc))

def result (e : StoredEdges.Edge) (rs : List Record) : List StoredHosts.Input :=
  (StoredHostPreparation.selected e rs).map Record.host

theorem records_trace (e : StoredEdges.Edge) (rs : List Record) :
    Trace (transition e) (StoredHostPreparation.scanSteps e rs+
      3*(StoredHostPreparation.selected e rs).length+4)
      (.prepare (.records rs [])) (.halt (result e rs)) := by
  have a := prepare_lift e (StoredHostPreparation.prepare_trace e rs)
  have c := copy_trace e (StoredHostPreparation.selected e rs) []
  simp only [List.append_nil] at c
  have d := reverse_trace e ((StoredHostPreparation.selected e rs).map Record.host).reverse []
  have middle := Trace.one (show transition e (.prepare (.halt (StoredHostPreparation.selected e rs)))=
    some (.copy (StoredHostPreparation.selected e rs) []) from rfl)
  convert a.trans (middle.trans (c.trans d)) using 1 <;>
    simp [result,List.length_reverse,List.length_map]
  omega

def inputBound (rs : List Record) : ℕ :=
  StoredHostPreparation.inputBound rs+2*rs.length+3

theorem steps_le_input (e : StoredEdges.Edge) (rs : List Record) :
    StoredHostPreparation.scanSteps e rs+3*(StoredHostPreparation.selected e rs).length+4 ≤ inputBound rs := by
  have a := StoredHostPreparation.steps_le_input e rs
  have b := StoredHostPreparation.selected_length_le e rs
  unfold inputBound
  omega
end LightEFTSpanners.StoredPreparedHostRecords

namespace LightEFTSpanners.StoredPreparedHostRecords
open StoredHostPreparation (Record)

def execute (e : StoredEdges.Edge) (rs : List Record) : List StoredHosts.Input :=
  match Controller.run (transition e) (inputBound rs) (.prepare (.records rs [])) with
  | .halt out => out
  | _ => []

theorem execute_eq (e : StoredEdges.Edge) (rs : List Record) :
    execute e rs=result e rs := by
  have hb := steps_le_input e rs
  let k := StoredHostPreparation.scanSteps e rs+3*(StoredHostPreparation.selected e rs).length+4
  have he : inputBound rs=k+(inputBound rs-k) := by dsimp [k];omega
  have run : Controller.run (transition e) (inputBound rs) (.prepare (.records rs []))=.halt (result e rs) := by
    rw [he,Controller.run_add,(records_trace e rs).run_eq]
    exact Controller.run_terminal _ _ rfl _
  simp [execute,run]

theorem execute_encoded {n : ℕ} (u v : Fin n) (rs : List (StoredHostPreparation.TypedRecord n)) :
    execute (u.val,v.val) (rs.map StoredHostPreparation.encode)=
      ((rs.filter (StoredHostPreparation.eligible u v)).map fun r => StoredHosts.encode r.host) := by
  rw [execute_eq]
  unfold result
  rw [←StoredHostPreparation.execute_eq,StoredHostPreparation.execute_encoded]
  simp [List.map_map,Function.comp_def,StoredHostPreparation.encode]
end LightEFTSpanners.StoredPreparedHostRecords
