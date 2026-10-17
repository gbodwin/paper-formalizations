import LightEFTSpanners.StoredSortSplit

namespace LightEFTSpanners.StoredSortSplit
open Controller

def bound (xs : List StoredEdges.Edge) : ℕ := 3*xs.length+3

theorem full_trace (xs : List StoredEdges.Edge) :
    ∃ k,k≤bound xs ∧ Trace (transition xs) k (.count xs 0)
      (.halt (xs.take ((xs.length+1)/2)) (xs.drop ((xs.length+1)/2))) := by
  let n := (xs.length+1)/2
  have a := count_trace xs xs 0
  simp only [Nat.zero_add] at a
  have b := split_trace xs xs [] n
  simp only [List.append_nil] at b
  have c := reverse_trace xs (xs.take n).reverse (xs.drop n) []
  simp only [List.reverse_reverse,List.append_nil] at c
  refine ⟨(xs.length+1)+(min n xs.length+1)+((xs.take n).reverse.length+1),?_,?_⟩
  · simp only [List.length_reverse,List.length_take]
    have h := Nat.min_le_right n xs.length
    unfold bound
    omega
  · simpa only [Nat.add_assoc] using a.trans (b.trans c)

def execute (xs : List StoredEdges.Edge) : List StoredEdges.Edge × List StoredEdges.Edge :=
  match Controller.run (transition xs) (bound xs) (.count xs 0) with
  | .halt left right => (left,right)
  | _ => ([],[])

theorem execute_eq (xs : List StoredEdges.Edge) :
    execute xs=(xs.take ((xs.length+1)/2),xs.drop ((xs.length+1)/2)) := by
  obtain ⟨k,hk,ht⟩ := full_trace xs
  have he : bound xs=k+(bound xs-k) := by omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]
end LightEFTSpanners.StoredSortSplit
