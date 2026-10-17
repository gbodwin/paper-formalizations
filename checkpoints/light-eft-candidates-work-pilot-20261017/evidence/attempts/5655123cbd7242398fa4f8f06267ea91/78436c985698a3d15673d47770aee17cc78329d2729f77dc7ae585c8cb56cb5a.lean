import LightEFTSpanners.StoredWeightMergeBound

namespace LightEFTSpanners.StoredWeightComparison

theorem result_encoded {n : ℕ} (bank : StoredOriginalWeightLookup.TypedBank n) (x y : Fin n × Fin n) :
    result (StoredOriginalWeightLookup.encode bank) (x.1.val,x.2.val) (y.1.val,y.2.val)=
      decide (StoredOriginalWeightLookup.weight s(y.1,y.2) bank≤StoredOriginalWeightLookup.weight s(x.1,x.2) bank) := by
  simp only [result,StoredOriginalWeightLookup.value_encoded]
end LightEFTSpanners.StoredWeightComparison

namespace LightEFTSpanners.StoredWeightMerge

theorem merge_encoded {n : ℕ} (bank : StoredOriginalWeightLookup.TypedBank n)
    (xs ys : List (Fin n × Fin n)) :
    List.merge (StoredEdges.encode xs) (StoredEdges.encode ys)
      (StoredWeightComparison.result (StoredOriginalWeightLookup.encode bank))=
      StoredEdges.encode (List.merge xs ys (fun x y => decide
        (StoredOriginalWeightLookup.weight s(y.1,y.2) bank≤StoredOriginalWeightLookup.weight s(x.1,x.2) bank))) := by
  induction xs generalizing ys with
  | nil => simp [StoredEdges.encode]
  | cons x xs ih =>
    induction ys with
    | nil => simp [StoredEdges.encode]
    | cons y ys iy =>
      simp only [StoredEdges.encode,List.map_cons,List.merge,StoredWeightComparison.result_encoded]
      split
      · simpa only [StoredEdges.encode,List.map_cons] using congrArg (List.cons (x.1.val,x.2.val)) (ih (y::ys))
      · simpa only [StoredEdges.encode,List.map_cons] using congrArg (List.cons (y.1.val,y.2.val)) iy

theorem execute_encoded {n : ℕ} (bank : StoredOriginalWeightLookup.TypedBank n)
    (xs ys : List (Fin n × Fin n)) :
    execute (StoredOriginalWeightLookup.encode bank) (StoredEdges.encode xs) (StoredEdges.encode ys)=
      StoredEdges.encode (List.merge xs ys (fun x y => decide
        (StoredOriginalWeightLookup.weight s(y.1,y.2) bank≤StoredOriginalWeightLookup.weight s(x.1,x.2) bank))) := by
  rw [execute_eq,merge_encoded]
end LightEFTSpanners.StoredWeightMerge
