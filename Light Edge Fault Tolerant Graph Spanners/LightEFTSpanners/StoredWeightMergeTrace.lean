import LightEFTSpanners.StoredWeightMerge

namespace LightEFTSpanners.StoredWeightMerge
open Controller

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

theorem merge_trace (bank : StoredOriginalWeightLookup.Bank) (xs ys acc : List StoredEdges.Edge) :
    Trace (transition bank) (work bank xs ys) (.merge xs ys acc)
      (.reverse ((List.merge xs ys (StoredWeightComparison.result bank)).reverse++acc) []) := by
  induction xs generalizing ys acc with
  | nil =>
    simpa [work_nil_left,work_nil_right,List.merge,Nat.add_comm,Nat.add_left_comm] using
      Trace.cons (show transition bank (.merge [] ys acc)=some (.copy ys acc) from rfl) (copy_trace bank ys acc)
  | cons x xs ih =>
    induction ys generalizing acc with
    | nil =>
      simpa [work_nil_left,work_nil_right,List.merge,Nat.add_comm,Nat.add_left_comm] using
        Trace.cons (show transition bank (.merge (x::xs) [] acc)=some (.copy (x::xs) acc) from rfl) (copy_trace bank (x::xs) acc)
    | cons y ys iy =>
      have a := Trace.one (show transition bank (.merge (x::xs) (y::ys) acc)=
        some (.compare x xs y ys acc (.first (.scan bank))) from rfl)
      have b := compare_lift bank x y xs ys acc (StoredWeightComparison.full_trace bank x y)
      cases hr : StoredWeightComparison.result bank x y with
      | true =>
        have c := Trace.one (show transition bank (.compare x xs y ys acc (.halt true))=
          some (.merge xs (y::ys) (x::acc)) from rfl)
        rw [hr] at b
        have d := a.trans (b.trans (c.trans (ih (y::ys) (x::acc))))
        have hc : 1+(StoredWeightComparison.steps bank x y+(1+work bank xs (y::ys)))=work bank (x::xs) (y::ys) := by
          simp [work_cons_cons,hr]
          omega
        rw [hc] at d
        simpa [List.merge,hr,List.reverse_cons,List.append_assoc] using d
      | false =>
        have c := Trace.one (show transition bank (.compare x xs y ys acc (.halt false))=
          some (.merge (x::xs) ys (y::acc)) from rfl)
        rw [hr] at b
        have d := a.trans (b.trans (c.trans (iy (y::acc))))
        have hc : 1+(StoredWeightComparison.steps bank x y+(1+work bank (x::xs) ys))=work bank (x::xs) (y::ys) := by
          simp [work_cons_cons,hr]
          omega
        rw [hc] at d
        simpa [List.merge,hr,List.reverse_cons,List.append_assoc] using d
end LightEFTSpanners.StoredWeightMerge
