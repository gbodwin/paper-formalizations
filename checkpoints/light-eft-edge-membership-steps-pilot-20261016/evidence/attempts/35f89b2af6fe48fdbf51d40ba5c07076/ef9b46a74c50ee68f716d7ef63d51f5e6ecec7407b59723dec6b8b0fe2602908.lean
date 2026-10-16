import LightEFTSpanners.StoredSortedCandidateExecutable

namespace LightEFTSpanners.StoredCandidateDrawLookup

def options (bank : Bank) : List StoredDrawLookup.Bank := []::bank.map Prod.snd

theorem value_mem (x : StoredEdges.Edge) (bank : Bank) : value x bank∈options bank := by
  induction bank with
  | nil => simp [value,options]
  | cons r rs ih =>
    simp only [value]
    split
    · simp [options]
    · simp only [options,List.map_cons,List.mem_cons] at ih ⊢
      tauto
end LightEFTSpanners.StoredCandidateDrawLookup

namespace LightEFTSpanners.StoredOriginalCandidateRecords

theorem value_length (Q : List StoredEdges.Edge) (bank : StoredCandidateDrawLookup.Bank) (xs : List StoredEdges.Edge) :
    (value Q bank xs).length≤xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [value_cons,List.length_cons]
    split
    · omega
    · simp only [List.length_cons]
      omega

theorem value_support (Q : List StoredEdges.Edge) (bank : StoredCandidateDrawLookup.Bank)
    (xs : List StoredEdges.Edge) (r : StoredForestBank.Input) (hr : r∈value Q bank xs) :
    r.edge∈xs ∧ r.bank∈StoredCandidateDrawLookup.options bank := by
  induction xs with
  | nil => simp [value] at hr
  | cons x xs ih =>
    simp only [value] at hr
    split at hr
    · obtain ⟨he,hb⟩ := ih hr
      exact ⟨List.mem_cons_of_mem _ he,hb⟩
    · rcases List.mem_cons.mp hr with he | he
      · subst r
        exact ⟨List.mem_cons_self,StoredCandidateDrawLookup.value_mem x bank⟩
      · obtain ⟨he,hb⟩ := ih he
        exact ⟨List.mem_cons_of_mem _ he,hb⟩
end LightEFTSpanners.StoredOriginalCandidateRecords
