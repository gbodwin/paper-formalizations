import LightEFTSpanners.StoredHostPreparationBound

namespace LightEFTSpanners.StoredHostPreparation

structure TypedRecord (n : ℕ) where
  id : ℕ
  eligibleEdges : List (Fin n × Fin n)
  host : StoredHosts.TypedInput n

def encode {n : ℕ} (r : TypedRecord n) : Record :=
  ⟨r.id,StoredEdges.encode r.eligibleEdges,StoredHosts.encode r.host⟩

def eligible {n : ℕ} (u v : Fin n) (r : TypedRecord n) : Bool :=
  decide (s(u,v)∈StoredSample.edgeSet r.eligibleEdges)

theorem contains_encode {n : ℕ} (u v : Fin n) (r : TypedRecord n) :
    StoredEdges.contains (u.val,v.val) (encode r).eligibleEdges=eligible u v r := by
  apply Bool.eq_iff_iff.mpr
  simp only [encode,eligible,decide_eq_true_eq,StoredEdges.contains_encode]
  simp [StoredSample.edgeSet]

theorem execute_encoded {n : ℕ} (u v : Fin n) (rs : List (TypedRecord n)) :
    execute (u.val,v.val) (rs.map encode)=((rs.filter (eligible u v)).map encode) := by
  rw [execute_eq]
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons,selected,List.filter_cons,contains_encode]
    cases h : eligible u v r <;> simp [selected] at ih ⊢ <;> exact ih
end LightEFTSpanners.StoredHostPreparation
