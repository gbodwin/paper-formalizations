import LightEFTSpanners.StoredOriginalCandidateSupport

namespace LightEFTSpanners.StoredSortedCandidateInput

theorem mem_le_sum (xs : List ℕ) (x : ℕ) (hx : x∈xs) : x≤xs.sum := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · simp
    · have hi := ih h
      simp only [List.sum_cons]
      omega

theorem map_sum_le {α : Type} (xs : List α) (f : α → ℕ) (C : ℕ) (h : ∀ x∈xs,f x≤C) :
    (xs.map f).sum≤xs.length*C := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul]
    omega

def preparationCap (n : ℕ) (fs : List (List StoredEdges.Edge)) (xs : List StoredEdges.Edge)
    (bank : StoredCandidateDrawLookup.Bank) : ℕ :=
  (xs.flatMap fun x => (StoredCandidateDrawLookup.options bank).map
    fun ds => StoredForestCandidate.bound n fs ds x+2).sum

def selectionCap (n q m : ℕ) (fs : List (List StoredEdges.Edge)) (bank : StoredCandidateDrawLookup.Bank) : ℕ :=
  ((StoredCandidateDrawLookup.options bank).map fun ds =>
    fs.length*n*(StoredForestCandidates.rawHostBound n q m fs ds+2)+3).sum

def callerBound (n : ℕ) (fs : List (List StoredEdges.Edge)) (Q E xs : List StoredEdges.Edge)
    (bank : StoredCandidateDrawLookup.Bank) : ℕ :=
  xs.length*preparationCap n fs xs bank+xs.length+3+
    xs.length*selectionCap n Q.length (E.length+xs.length) fs bank+1

theorem forest_bound_le (n : ℕ) (fs : List (List StoredEdges.Edge)) (Q E xs : List StoredEdges.Edge)
    (bank : StoredCandidateDrawLookup.Bank) (rs : List StoredForestBank.Input)
    (len : rs.length≤xs.length) (support : ∀ r∈rs,r.edge∈xs ∧ r.bank∈StoredCandidateDrawLookup.options bank) :
    StoredForestCandidates.bound n fs Q E rs≤callerBound n fs Q E xs bank := by
  have prep : ∀ r∈rs,StoredForestCandidate.bound n fs r.bank r.edge+2≤preparationCap n fs xs bank := by
    intro r hr
    obtain ⟨he,hb⟩ := support r hr
    apply mem_le_sum
    exact List.mem_flatMap.mpr ⟨r.edge,he,List.mem_map.mpr ⟨r.bank,hb,rfl⟩⟩
  have sel : ∀ r∈rs,fs.length*n*(StoredForestCandidates.rawHostBound n Q.length (E.length+rs.length) fs r.bank+2)+3≤
      selectionCap n Q.length (E.length+xs.length) fs bank := by
    intro r hr
    have hm : StoredForestCandidates.rawHostBound n Q.length (E.length+rs.length) fs r.bank≤
        StoredForestCandidates.rawHostBound n Q.length (E.length+xs.length) fs r.bank := by
      unfold StoredForestCandidates.rawHostBound
      gcongr
    apply le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hm 2)) 3)
    apply mem_le_sum
    exact List.mem_map.mpr ⟨r.bank,(support r hr).2,rfl⟩
  have hp := map_sum_le rs _ _ prep
  have hs := map_sum_le rs _ _ sel
  have hp' := Nat.mul_le_mul_right (preparationCap n fs xs bank) len
  have hs' := Nat.mul_le_mul_right (selectionCap n Q.length (E.length+xs.length) fs bank) len
  unfold StoredForestCandidates.bound StoredForestBank.bound StoredForestBank.scanBound
    StoredForestCandidates.selectionBound callerBound
  omega
end LightEFTSpanners.StoredSortedCandidateInput

namespace LightEFTSpanners.StoredSortedCandidateInput

theorem prepared_bound (n : ℕ) (fs : List (List StoredEdges.Edge)) (Q E xs : List StoredEdges.Edge)
    (weights : StoredOriginalWeightLookup.Bank) (bank : StoredCandidateDrawLookup.Bank) :
    StoredForestCandidates.bound n fs Q E (execute weights Q bank xs)≤callerBound n fs Q E xs bank := by
  apply forest_bound_le
  · rw [execute_eq,List.length_reverse]
    exact (StoredOriginalCandidateRecords.value_length Q bank _).trans (by simp)
  · intro r hr
    rw [execute_eq,List.mem_reverse] at hr
    obtain ⟨he,hb⟩ := StoredOriginalCandidateRecords.value_support Q bank _ r hr
    exact ⟨(List.mergeSort_perm xs (StoredWeightComparison.result weights)).mem_iff.mp he,hb⟩
end LightEFTSpanners.StoredSortedCandidateInput
