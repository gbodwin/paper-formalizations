import LightEFTSpanners.StoredForestInput

namespace LightEFTSpanners.StoredForestInput
open Controller

theorem full_trace {n : ℕ} (fs : List (List (Fin n × Fin n))) (bank : StoredDrawLookup.Bank) :
    ∃ k,k≤bound n (fs.map StoredEdges.encode) bank ∧ Trace (transition n bank) k
      (.forests (.forests 0 (fs.map StoredEdges.encode) [])) (.halt (value fs bank)) := by
  obtain ⟨k,hk,ht⟩ := StoredForestHosts.full_trace fs
  have a := forests_lift n bank ht
  have b := Trace.one (show transition n bank (.forests (.halt (StoredForestHosts.value 0 fs)))=
    some (.attach (.records (StoredForestHosts.value 0 fs) [])) from rfl)
  have c := attach_lift n bank (StoredForestDrawAttachment.attachment_trace n bank (StoredForestHosts.value 0 fs))
  have d := Trace.one (show transition n bank (.attach (.halt (value fs bank)))=some (.halt (value fs bank)) from rfl)
  have hs := StoredForestDrawAttachment.steps_le n bank (StoredForestHosts.value 0 fs)
  have hl := StoredForestHosts.value_length fs 0
  have hm : StoredForestDrawAttachment.bound bank (StoredForestHosts.value 0 fs).length≤
      StoredForestDrawAttachment.bound bank (fs.length*n) := by
    unfold StoredForestDrawAttachment.bound
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) _
  refine ⟨k+1+StoredForestDrawAttachment.steps n bank (StoredForestHosts.value 0 fs)+1,?_,?_⟩
  · simp only [bound,List.length_map]
    omega
  · simpa [value,Nat.add_assoc] using a.trans (b.trans (c.trans d))

theorem execute_eq {n : ℕ} (fs : List (List (Fin n × Fin n))) (bank : StoredDrawLookup.Bank) :
    execute n (fs.map StoredEdges.encode) bank=value fs bank := by
  obtain ⟨k,hk,ht⟩ := full_trace fs bank
  have he : bound n (fs.map StoredEdges.encode) bank=k+(bound n (fs.map StoredEdges.encode) bank-k) := by omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]
end LightEFTSpanners.StoredForestInput
