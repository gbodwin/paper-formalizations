import LightEFTSpanners.StoredForestCandidate

namespace LightEFTSpanners.StoredForestCandidate
open Controller

theorem full_trace {n : ℕ} (fs : List (List (Fin n × Fin n))) (bank : StoredDrawLookup.Bank)
    (e : StoredEdges.Edge) (W : StoredRecords.Weights) (t : ℚ) :
    ∃ k,k≤bound n (fs.map StoredEdges.encode) bank e ∧ Trace (transition n bank e W t) k
      (.inputs (.forests (.forests 0 (fs.map StoredEdges.encode) []))) (.halt (value fs bank e W t)) := by
  obtain ⟨k,hk,ht⟩ := StoredForestInput.full_trace fs bank
  let r : StoredComponentCandidate.Input := ⟨e,StoredForestInput.value fs bank⟩
  have a := inputs_lift n bank e W t ht
  have b := Trace.one (show transition n bank e W t (.inputs (.halt (StoredForestInput.value fs bank)))=
    some (.candidate (.catalogue r (.inputs r.components []))) from rfl)
  have c := candidate_lift n bank e W t (StoredComponentCandidate.candidate_trace W t r)
  have d := Trace.one (show transition n bank e W t (.candidate (.candidate (.halt (value fs bank e W t))))=
    some (.halt (value fs bank e W t)) from rfl)
  have hs := StoredComponentCandidate.steps_le_input W r
  have hb := component_input_bound n e (StoredForestInput.value fs bank) (StoredForestInput.vertices_length fs bank)
  have hl := StoredForestInput.value_length fs bank
  have hm : componentBound n (StoredForestInput.value fs bank).length e≤componentBound n (fs.length*n) e := by
    unfold componentBound
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) _) _) _
  refine ⟨k+1+StoredComponentCandidate.steps W r+1,?_,?_⟩
  · simp only [bound,List.length_map]
    change StoredComponentCandidate.steps W r≤StoredComponentCandidate.inputBound ⟨e,StoredForestInput.value fs bank⟩ at hs
    omega
  · simpa [value,r,Nat.add_assoc] using a.trans (b.trans (c.trans d))

theorem execute_eq {n : ℕ} (fs : List (List (Fin n × Fin n))) (bank : StoredDrawLookup.Bank)
    (e : StoredEdges.Edge) (W : StoredRecords.Weights) (t : ℚ) :
    execute n (fs.map StoredEdges.encode) bank e W t=some (value fs bank e W t) := by
  obtain ⟨k,hk,ht⟩ := full_trace fs bank e W t
  have he : bound n (fs.map StoredEdges.encode) bank e=k+(bound n (fs.map StoredEdges.encode) bank e-k) := by omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]
end LightEFTSpanners.StoredForestCandidate
