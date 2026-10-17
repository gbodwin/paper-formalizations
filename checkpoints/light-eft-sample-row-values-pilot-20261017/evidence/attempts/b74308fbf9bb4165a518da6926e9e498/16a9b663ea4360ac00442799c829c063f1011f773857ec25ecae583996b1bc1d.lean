import LightEFTSpanners.StoredCandidatePreparation

namespace LightEFTSpanners.StoredCandidatePreparation
structure TypedInput (n : ℕ) where
  edge : Fin n × Fin n
  catalogue : List (StoredHostPreparation.TypedRecord n)

def encode {n : ℕ} (r : TypedInput n) : Input :=
  ⟨(r.edge.1.val,r.edge.2.val),r.catalogue.map StoredHostPreparation.encode⟩

def typedResult {n : ℕ} (w : Sym2 (Fin n) → ℚ) (t : ℚ) (r : TypedInput n) : StoredCandidates.TypedInput n :=
  ⟨r.edge,t*w s(r.edge.1,r.edge.2),
    (r.catalogue.filter (StoredHostPreparation.eligible r.edge.1 r.edge.2)).map StoredHostPreparation.TypedRecord.host⟩

theorem result_encoded {n : ℕ} (w : Sym2 (Fin n) → ℚ) (t : ℚ) (r : TypedInput n) :
    result (StoredRecords.encodeWeights w) t (encode r)=StoredCandidates.encode (typedResult w t r) := by
  have hs := StoredPreparedHostRecords.execute_encoded r.edge.1 r.edge.2 r.catalogue
  rw [StoredPreparedHostRecords.execute_eq] at hs
  simp only [result,encode,StoredWeightLookup.value_encoded,typedResult,StoredCandidates.encode,
    List.map_map,Function.comp_def]
  rw [hs]

def execute (W : StoredRecords.Weights) (t : ℚ) (r : Input) : StoredCandidates.Input :=
  match Controller.run (transition W t) (inputBound r) (start W r) with
  | .halt out => out
  | _ => ⟨r.edge,0,[]⟩

theorem execute_eq (W : StoredRecords.Weights) (t : ℚ) (r : Input) : execute W t r=result W t r := by
  have hb := steps_le W r
  have he : inputBound r=steps W r+(inputBound r-steps W r) := by omega
  unfold execute
  rw [he,Controller.run_add,(prepare_trace W t r).run_eq,Controller.run_terminal _ _ rfl]

theorem execute_encoded {n : ℕ} (w : Sym2 (Fin n) → ℚ) (t : ℚ) (r : TypedInput n) :
    execute (StoredRecords.encodeWeights w) t (encode r)=StoredCandidates.encode (typedResult w t r) := by
  rw [execute_eq,result_encoded]
end LightEFTSpanners.StoredCandidatePreparation
