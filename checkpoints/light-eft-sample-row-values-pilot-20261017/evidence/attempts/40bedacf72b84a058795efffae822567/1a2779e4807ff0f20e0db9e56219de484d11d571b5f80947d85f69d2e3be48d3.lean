import LightEFTSpanners.StoredHostPreparation

namespace LightEFTSpanners.StoredHostPreparation

def inputBound (rs : List Record) : ℕ :=
  (rs.map fun r => r.eligibleEdges.length+3).sum+rs.length+2

theorem scanSteps_le (e : StoredEdges.Edge) (rs : List Record) :
    scanSteps e rs ≤ (rs.map fun r => r.eligibleEdges.length+3).sum+1 := by
  induction rs with
  | nil => simp [scanSteps_nil]
  | cons r rs ih =>
    have h := StoredEdges.steps_le e r.eligibleEdges
    simp only [scanSteps_cons,List.map_cons,List.sum_cons]
    omega

theorem selected_length_le (e : StoredEdges.Edge) (rs : List Record) :
    (selected e rs).length≤rs.length := List.length_filter_le _ _

theorem steps_le_input (e : StoredEdges.Edge) (rs : List Record) :
    scanSteps e rs+(selected e rs).length+1 ≤ inputBound rs := by
  have a := scanSteps_le e rs
  have c := selected_length_le e rs
  unfold inputBound
  omega

def execute (e : StoredEdges.Edge) (rs : List Record) : List Record :=
  match Controller.run (transition e) (inputBound rs) (.records rs []) with
  | .halt out => out
  | _ => []

theorem run_prepare (e : StoredEdges.Edge) (rs : List Record) :
    Controller.run (transition e) (inputBound rs) (.records rs [])=.halt (selected e rs) := by
  have hb := steps_le_input e rs
  have he : inputBound rs=(scanSteps e rs+(selected e rs).length+1)+
      (inputBound rs-(scanSteps e rs+(selected e rs).length+1)) := by omega
  rw [he,Controller.run_add,(prepare_trace e rs).run_eq]
  exact Controller.run_terminal _ _ rfl _

@[simp] theorem execute_eq (e : StoredEdges.Edge) (rs : List Record) :
    execute e rs=selected e rs := by simp [execute,run_prepare]

theorem execute_sublist (e : StoredEdges.Edge) (rs : List Record) :
    (execute e rs).Sublist rs := by
  rw [execute_eq]
  exact List.filter_sublist
end LightEFTSpanners.StoredHostPreparation
