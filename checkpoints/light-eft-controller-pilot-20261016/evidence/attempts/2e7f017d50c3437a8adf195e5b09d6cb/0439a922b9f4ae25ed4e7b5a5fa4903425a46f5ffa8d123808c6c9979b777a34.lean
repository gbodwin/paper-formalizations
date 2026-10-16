import LightEFTSpanners.StoredFlagBatchTrace
import LightEFTSpanners.StoredFlagSampleEncoding

namespace LightEFTSpanners.StoredFlagBatch
def execute (xs : Input) : Output :=
  match Controller.run transition (budget xs) (.next xs []) with | .halt es => es | _ => []

theorem execute_eq (xs : Input) : execute xs=value xs := by
  obtain ⟨k,hk,ht⟩ := full_trace xs
  have he : budget xs=k+(budget xs-k) := by omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]

theorem input_budget (xs : Input) : budget xs=2*(xs.map List.length).sum+5*xs.length+2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [budget,List.map_cons,List.sum_cons,StoredFlagSample.bound,List.length_cons] at *
    omega

theorem execute_encoded {n : ℕ} (bits : List (Sym2 (Fin n) → Bool)) :
    execute (bits.map StoredFlagSample.entries)=
      bits.map (fun b => StoredEdges.encode (StoredFlagSample.typed b)) := by
  rw [execute_eq]
  unfold value
  rw [List.map_map]
  apply List.map_congr_left
  intro b _
  change StoredFlagSample.value (StoredFlagSample.entries b)=_
  rw [←StoredFlagSample.execute_eq,StoredFlagSample.execute_encoded]
end LightEFTSpanners.StoredFlagBatch
