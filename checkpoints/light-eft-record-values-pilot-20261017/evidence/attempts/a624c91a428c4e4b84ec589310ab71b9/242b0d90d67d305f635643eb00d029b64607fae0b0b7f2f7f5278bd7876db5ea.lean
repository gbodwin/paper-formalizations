import LightEFTSpanners.StoredComponentCatalogue

namespace LightEFTSpanners.StoredComponentCatalogue
open StoredComponentRecord

theorem result_encoded {n : ℕ} (rs : List (TypedInput n)) :
    result (rs.map encode)=(rs.map typedResult).map StoredHostPreparation.encode := by
  simp only [result,List.map_map,Function.comp_def,StoredComponentRecord.result_encoded]

def execute (rs : List Input) : List StoredHostPreparation.Record :=
  match Controller.run transition (inputBound rs) (.inputs rs []) with
  | .halt out => out
  | _ => []

theorem execute_eq (rs : List Input) : execute rs=result rs := by
  have hb := steps_le_input rs
  have he : inputBound rs=(scanSteps rs+rs.length+1)+(inputBound rs-(scanSteps rs+rs.length+1)) := by omega
  unfold execute
  rw [he,Controller.run_add,(bank_trace rs).run_eq,Controller.run_terminal _ _ rfl]

theorem execute_encoded {n : ℕ} (rs : List (TypedInput n)) :
    execute (rs.map encode)=(rs.map typedResult).map StoredHostPreparation.encode := by
  rw [execute_eq,result_encoded]
end LightEFTSpanners.StoredComponentCatalogue
