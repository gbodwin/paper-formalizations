import LightEFTSpanners.StoredWeightMerge

namespace LightEFTSpanners.StoredWeightMerge
open Controller

def work (bank : StoredOriginalWeightLookup.Bank) : List StoredEdges.Edge → List StoredEdges.Edge → ℕ
  | [],ys => ys.length+2
  | xs,[] => xs.length+2
  | x::xs,y::ys => StoredWeightComparison.steps bank x y+2+
      if StoredWeightComparison.result bank x y then work bank xs (y::ys) else work bank (x::xs) ys
termination_by xs ys => xs.length+ys.length

theorem merge_trace (bank : StoredOriginalWeightLookup.Bank) (xs ys acc : List StoredEdges.Edge) :
    Trace (transition bank) (work bank xs ys) (.merge xs ys acc)
      (.reverse ((List.merge xs ys (StoredWeightComparison.result bank)).reverse++acc) []) := by
  induction xs generalizing ys acc with
  | nil =>
    simpa [work,List.merge,Nat.add_comm,Nat.add_left_comm] using
      Trace.cons (show transition bank (.merge [] ys acc)=some (.copy ys acc) from rfl) (copy_trace bank ys acc)
  | cons x xs ih =>
    induction ys generalizing acc with
    | nil =>
      simpa [work,List.merge,Nat.add_comm,Nat.add_left_comm] using
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
          simp [work,hr]
          omega
        rw [hc] at d
        simpa [List.merge,hr,List.reverse_cons,List.append_assoc] using d
      | false =>
        have c := Trace.one (show transition bank (.compare x xs y ys acc (.halt false))=
          some (.merge (x::xs) ys (y::acc)) from rfl)
        rw [hr] at b
        have d := a.trans (b.trans (c.trans (iy (y::acc))))
        have hc : 1+(StoredWeightComparison.steps bank x y+(1+work bank (x::xs) ys))=work bank (x::xs) (y::ys) := by
          simp [work,hr]
          omega
        rw [hc] at d
        simpa [List.merge,hr,List.reverse_cons,List.append_assoc] using d
end LightEFTSpanners.StoredWeightMerge
