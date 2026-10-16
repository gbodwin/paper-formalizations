import LightEFTSpanners.StoredWeightSort

namespace LightEFTSpanners.StoredWeightSort
open Controller

theorem sort_trace (bank : StoredOriginalWeightLookup.Bank) (xs : List StoredEdges.Edge) (stack : List Frame) :
    ∃ k,Trace (transition bank) k (.sort xs stack)
      (.returning (xs.mergeSort (StoredWeightComparison.result bank)) stack) := by
  generalize hn : xs.length=n
  induction n using Nat.strong_induction_on generalizing xs stack with
  | h n ih =>
    cases xs with
    | nil => exact ⟨1,Trace.one (by simp [transition])⟩
    | cons x tail =>
      cases tail with
      | nil => exact ⟨1,Trace.one (by simp [transition])⟩
      | cons y rest =>
        let original := x::y::rest
        let half := (original.length+1)/2
        let left := original.take half
        let right := original.drop half
        have hl : left.length<n := by simp [left,half,original,List.length_cons] at hn ⊢;omega
        have hr : right.length<n := by simp [right,half,original,List.length_cons] at hn ⊢;omega
        obtain ⟨a,ha⟩ := ih left.length hl left (.right right::stack) rfl
        obtain ⟨b,hb⟩ := ih right.length hr right (.merge (left.mergeSort (StoredWeightComparison.result bank))::stack) rfl
        obtain ⟨c,_,hc⟩ := StoredSortSplit.full_trace original
        have hc := split_lift bank original stack hc
        obtain ⟨d,_,hd⟩ := StoredWeightMerge.full_trace bank
          (left.mergeSort (StoredWeightComparison.result bank)) (right.mergeSort (StoredWeightComparison.result bank))
        have hd := merge_lift bank stack hd
        have e0 := Trace.one (show transition bank (.sort original stack)=some (.split original stack (.count original 0)) from rfl)
        have e1 := Trace.one (show transition bank (.split original stack (.halt left right))=some (.sort left (.right right::stack)) from rfl)
        have e2 := Trace.one (show transition bank (.returning (left.mergeSort (StoredWeightComparison.result bank)) (.right right::stack))=
          some (.sort right (.merge (left.mergeSort (StoredWeightComparison.result bank))::stack)) from rfl)
        have e3 := Trace.one (show transition bank (.returning (right.mergeSort (StoredWeightComparison.result bank))
            (.merge (left.mergeSort (StoredWeightComparison.result bank))::stack))=
          some (.merging stack (.merge (left.mergeSort (StoredWeightComparison.result bank))
            (right.mergeSort (StoredWeightComparison.result bank)) [])) from rfl)
        have e4 := Trace.one (show transition bank (.merging stack (.halt (List.merge
            (left.mergeSort (StoredWeightComparison.result bank)) (right.mergeSort (StoredWeightComparison.result bank))
            (StoredWeightComparison.result bank))))=
          some (.returning (List.merge (left.mergeSort (StoredWeightComparison.result bank))
            (right.mergeSort (StoredWeightComparison.result bank)) (StoredWeightComparison.result bank)) stack) from rfl)
        have he : (x::y::rest).mergeSort (StoredWeightComparison.result bank)=
            List.merge (left.mergeSort (StoredWeightComparison.result bank))
              (right.mergeSort (StoredWeightComparison.result bank)) (StoredWeightComparison.result bank) := by
          rw [List.mergeSort]
          simp only [List.MergeSort.Internal.splitInTwo,List.splitAt_eq]
          rfl
        rw [he]
        exact ⟨_,e0.trans (hc.trans (e1.trans (ha.trans (e2.trans (hb.trans (e3.trans (hd.trans e4)))))))⟩
end LightEFTSpanners.StoredWeightSort
