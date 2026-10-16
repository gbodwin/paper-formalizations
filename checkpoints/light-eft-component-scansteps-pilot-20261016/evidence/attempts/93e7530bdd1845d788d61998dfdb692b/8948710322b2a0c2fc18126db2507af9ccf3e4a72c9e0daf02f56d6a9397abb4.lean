import LightEFTSpanners.StoredForestInputSize

namespace LightEFTSpanners.StoredForestCandidate

def componentBound (n q : ℕ) (e : StoredEdges.Edge) : ℕ := q*(3*n*n+2*n+12)+e.1+e.2+12

theorem component_input_bound (n : ℕ) (e : StoredEdges.Edge) (rs : List StoredComponentRecord.Input)
    (h : ∀ r∈rs,r.vertices.length≤n) :
    StoredComponentCandidate.inputBound ⟨e,rs⟩≤componentBound n rs.length e := by
  induction rs with
  | nil =>
    simp [StoredComponentCandidate.inputBound,StoredComponentCatalogue.inputBound,componentBound]
    omega
  | cons r rs ih =>
    have hr := h r (by simp)
    have ht := ih (fun s hs => h s (by simp [hs]))
    have hs : r.vertices.length*r.vertices.length≤n*n := Nat.mul_self_le_mul_self hr
    simp only [StoredComponentCandidate.inputBound,StoredComponentCatalogue.inputBound,
      StoredComponentRecord.steps,StoredVertexPairs.steps,List.map_cons,List.sum_cons,List.length_cons,
      componentBound,Nat.add_mul] at *
    nlinarith
end LightEFTSpanners.StoredForestCandidate
