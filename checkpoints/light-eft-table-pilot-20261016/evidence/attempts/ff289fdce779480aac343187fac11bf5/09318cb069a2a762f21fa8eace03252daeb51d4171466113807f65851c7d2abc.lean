import LightEFTSpanners.StoredForestHostsTrace

namespace LightEFTSpanners.StoredForestHosts
open Controller

def bound (n : ℕ) (fs : List (List StoredEdges.Edge)) : ℕ := inputBound n fs+fs.length*n+1

def execute (n : ℕ) (fs : List (List StoredEdges.Edge)) : List Record :=
  match Controller.run (transition n) (bound n fs) (.forests 0 fs []) with
  | .halt rs => rs
  | _ => []

theorem full_trace {n : ℕ} (fs : List (List (Fin n × Fin n))) :
    ∃ k,k≤bound n (fs.map StoredEdges.encode) ∧ Trace (transition n) k
      (.forests 0 (fs.map StoredEdges.encode) []) (.halt (value 0 fs)) := by
  obtain ⟨k,hk,ht⟩ := scan_trace fs 0 []
  simp only [List.append_nil] at ht
  have hu := reverse_trace n (value 0 fs).reverse []
  have hl := value_length fs 0
  refine ⟨k+((value 0 fs).length+1),?_,?_⟩
  · simp only [bound,List.length_map]
    omega
  · simpa using ht.trans hu

theorem execute_eq {n : ℕ} (fs : List (List (Fin n × Fin n))) :
    execute n (fs.map StoredEdges.encode)=value 0 fs := by
  obtain ⟨k,hk,ht⟩ := full_trace fs
  have he : bound n (fs.map StoredEdges.encode)=k+(bound n (fs.map StoredEdges.encode)-k) := by omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]
end LightEFTSpanners.StoredForestHosts
