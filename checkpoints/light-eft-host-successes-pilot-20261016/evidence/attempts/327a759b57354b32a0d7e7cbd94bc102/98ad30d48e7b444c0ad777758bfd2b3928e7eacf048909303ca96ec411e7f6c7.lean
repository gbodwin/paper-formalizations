import LightEFTSpanners.StoredCandidateBankPreparation

namespace LightEFTSpanners.StoredCandidateBankPreparation
open StoredCandidatePreparation

theorem result_encoded {n : ℕ} (w : Sym2 (Fin n) → ℚ) (t : ℚ)
    (rs : List (TypedInput n)) :
    result (StoredRecords.encodeWeights w) t (rs.map encode)=
      (rs.map (typedResult w t)).map StoredCandidates.encode := by
  simp only [result,List.map_map,Function.comp_def,StoredCandidatePreparation.result_encoded]

def execute (W : StoredRecords.Weights) (t : ℚ) (rs : List Input) : List StoredCandidates.Input :=
  match Controller.run (transition W t) (inputBound rs) (.inputs rs []) with
  | .halt out => out
  | _ => []

theorem execute_eq (W : StoredRecords.Weights) (t : ℚ) (rs : List Input) :
    execute W t rs=result W t rs := by
  have hb := steps_le_input W rs
  have he : inputBound rs=(scanSteps W rs+rs.length+1)+
    (inputBound rs-(scanSteps W rs+rs.length+1)) := by omega
  unfold execute
  rw [he,Controller.run_add,(bank_trace W t rs).run_eq,Controller.run_terminal _ _ rfl]

theorem execute_encoded {n : ℕ} (w : Sym2 (Fin n) → ℚ) (t : ℚ)
    (rs : List (TypedInput n)) :
    execute (StoredRecords.encodeWeights w) t (rs.map encode)=
      (rs.map (typedResult w t)).map StoredCandidates.encode := by
  rw [execute_eq,result_encoded]
end LightEFTSpanners.StoredCandidateBankPreparation
