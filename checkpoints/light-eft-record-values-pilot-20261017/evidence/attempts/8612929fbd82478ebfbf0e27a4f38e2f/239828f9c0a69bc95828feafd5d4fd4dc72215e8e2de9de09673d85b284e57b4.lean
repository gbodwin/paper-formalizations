import LightEFTSpanners.StoredSampleEntry

/-! Literal endpoint lists encode the four finite edge sets. Orientation and
repetition do not affect membership, but their actual cells remain charged. -/
namespace LightEFTSpanners.StoredSample

def edgeSet {n : ℕ} (es : List (Fin n × Fin n)) : Finset (Sym2 (Fin n)) :=
  (es.map fun e => s(e.1,e.2)).toFinset

def encodeLists {n : ℕ} (Q E T S : List (Fin n × Fin n)) : EdgeLists :=
  ⟨StoredEdges.encode Q,StoredEdges.encode E,StoredEdges.encode T,StoredEdges.encode S⟩

theorem contains_edgeSet {n : ℕ} (u v : Fin n) (es : List (Fin n × Fin n)) :
    StoredEdges.contains (u.val,v.val) (StoredEdges.encode es)=decide (s(u,v)∈edgeSet es) := by
  apply Bool.eq_iff_iff.mpr
  simpa [edgeSet] using StoredEdges.contains_encode u v es

theorem entry_encoded {n : ℕ} (Q E T S : List (Fin n × Fin n))
    (w : ℚ) (u v : Fin n) :
    entry (u.val,v.val) w (encodeLists Q E T S)=
      ⟨w,decide (s(u,v)∈edgeSet Q),decide (s(u,v)∈edgeSet E),
        decide (s(u,v)∈edgeSet T),decide (s(u,v)∈edgeSet S)⟩ := by
  simp only [entry,encodeLists,contains_edgeSet]
end LightEFTSpanners.StoredSample
