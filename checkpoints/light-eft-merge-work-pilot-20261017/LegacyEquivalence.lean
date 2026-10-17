import LightEFTSpanners.StoredWeightMergeTrace
namespace LightEFTSpanners.StoredWeightMerge.WorkComparison
def work (bank : StoredOriginalWeightLookup.Bank) : List StoredEdges.Edge → List StoredEdges.Edge → ℕ :=
  List.rec (motive := fun _ => List StoredEdges.Edge → ℕ)
    (fun ys => ys.length+2)
    (fun x xs next => List.rec (motive := fun _ => ℕ) ((x::xs).length+2)
      (fun y ys rest => StoredWeightComparison.steps bank x y+2+
        if StoredWeightComparison.result bank x y then next (y::ys) else rest))

theorem work_nil_left (bank : StoredOriginalWeightLookup.Bank) (ys : List StoredEdges.Edge) :
    work bank [] ys = ys.length+2 := rfl

theorem work_nil_right (bank : StoredOriginalWeightLookup.Bank) (xs : List StoredEdges.Edge) :
    work bank xs [] = xs.length+2 := by cases xs <;> rfl

theorem work_cons_cons (bank : StoredOriginalWeightLookup.Bank) (x y : StoredEdges.Edge)
    (xs ys : List StoredEdges.Edge) :
    work bank (x::xs) (y::ys) = StoredWeightComparison.steps bank x y+2+
      if StoredWeightComparison.result bank x y then work bank xs (y::ys) else work bank (x::xs) ys := rfl

theorem work_eq_prior (bank : StoredOriginalWeightLookup.Bank) (xs ys : List StoredEdges.Edge) :
    work bank xs ys = LightEFTSpanners.StoredWeightMerge.work bank xs ys := by
  induction xs generalizing ys with
  | nil => simp only [work_nil_left,LightEFTSpanners.StoredWeightMerge.work]
  | cons x xs ih =>
    induction ys with
    | nil => simp only [work_nil_right,LightEFTSpanners.StoredWeightMerge.work]
    | cons y ys iy =>
      rw [work_cons_cons,LightEFTSpanners.StoredWeightMerge.work]
      rw [ih,iy]
#print axioms work_eq_prior
end LightEFTSpanners.StoredWeightMerge.WorkComparison
