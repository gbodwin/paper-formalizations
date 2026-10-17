import LightEFTSpanners.StoredCanonicalEnumeration

namespace LightEFTSpanners.StoredCanonicalEnumeration
open Controller

def bound (n m : ℕ) : ℕ := n*(StoredCanonicalRoot.bound n m+3)+n+3

def execute (n : ℕ) (edges : List StoredEdges.Edge) : List Record :=
  match Controller.run (transition n edges) (bound n edges.length) (.range n []) with
  | .halt out => out
  | _ => []

theorem full_trace {n : ℕ} (edges : List (Fin n × Fin n)) :
    ∃ k,k≤bound n edges.length ∧ Trace (transition n (StoredEdges.encode edges)) k
      (.range n []) (.halt (values edges (List.finRange n))) := by
  have a := range_trace n (StoredEdges.encode edges) n []
  obtain ⟨k,hk,hb⟩ := roots_trace edges (List.finRange n) []
  have he : (List.finRange n).map Fin.val=List.range n := by simp
  rw [he] at hb
  simp only [List.append_nil] at a hb
  have c := reverse_trace n (StoredEdges.encode edges) (values edges (List.finRange n)).reverse []
  have hl : (values edges (List.finRange n)).length≤n := by
    simpa [values] using List.length_filterMap_le
      (fun r : Fin n => (StoredCanonicalRoot.result edges r).map fun vs => (r.val,vs)) (List.finRange n)
  refine ⟨n+1+k+((values edges (List.finRange n)).length+1),?_,?_⟩
  · simp only [List.length_finRange] at hk
    unfold bound
    have hmul : n*(StoredCanonicalRoot.bound n edges.length+3)=
        n*(StoredCanonicalRoot.bound n edges.length+2)+n := by ring
    rw [hmul]
    omega
  · simpa [Nat.add_assoc] using a.trans (hb.trans c)

theorem execute_eq {n : ℕ} (edges : List (Fin n × Fin n)) :
    execute n (StoredEdges.encode edges)=values edges (List.finRange n) := by
  obtain ⟨k,hk,ht⟩ := full_trace edges
  have he : bound n (StoredEdges.encode edges).length=k+(bound n (StoredEdges.encode edges).length-k) := by
    simp only [StoredEdges.encode,List.length_map]
    omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]
end LightEFTSpanners.StoredCanonicalEnumeration
