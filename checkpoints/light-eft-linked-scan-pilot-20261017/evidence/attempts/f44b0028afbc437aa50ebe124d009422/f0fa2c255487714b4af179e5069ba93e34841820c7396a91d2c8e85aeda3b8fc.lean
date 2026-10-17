import LightEFTSpanners.VotingAdmissionHistory
import LightEFTSpanners.SamplingRestriction

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners
variable {V J : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Keep exactly this host's actually assigned records selected by this sample. -/
noncomputable def selectedList (j : J) (S : Finset (Sym2 V)) :
    List (Sym2 V × Finset J) → List (Sym2 V)
  | [] => []
  | (e,A)::rs => if j∈A ∧ e∈S then e::selectedList j S rs else selectedList j S rs

 theorem selectedList_sublist (j : J) (S : Finset (Sym2 V)) (rs : List (Sym2 V × Finset J)) :
    (selectedList j S rs).Sublist (rs.map Prod.fst) := by
  induction rs with
  | nil => exact List.Sublist.refl _
  | cons r rs ih =>
    obtain ⟨e,A⟩ := r
    simp only [selectedList,List.map_cons]
    split_ifs
    · exact ih.cons_cons e
    · exact ih.cons e

 theorem selectedList_mem_sample (j : J) (S : Finset (Sym2 V))
    (rs : List (Sym2 V × Finset J)) {e : Sym2 V} (he : e∈selectedList j S rs) : e∈S := by
  induction rs with
  | nil => simp [selectedList] at he
  | cons r rs ih =>
    obtain ⟨d,A⟩ := r
    simp only [selectedList] at he
    split_ifs at he with hh
    · rcases List.mem_cons.mp he with rfl | he
      · exact hh.2
      · exact ih he
    · exact ih he

 theorem selectedList_record (j : J) (S : Finset (Sym2 V))
    (rs : List (Sym2 V × Finset J)) {e : Sym2 V} (he : e∈selectedList j S rs) :
    ∃ A,(e,A)∈rs ∧ j∈A := by
  induction rs with
  | nil => simp [selectedList] at he
  | cons r rs ih =>
    obtain ⟨d,A⟩ := r
    simp only [selectedList] at he
    split_ifs at he with hh
    · rcases List.mem_cons.mp he with rfl | he
      · exact ⟨A,by simp,hh.1⟩
      · obtain ⟨B,hB,hj⟩ := ih he
        exact ⟨B,List.mem_cons_of_mem _ hB,hj⟩
    · obtain ⟨B,hB,hj⟩ := ih he
      exact ⟨B,List.mem_cons_of_mem _ hB,hj⟩

 theorem selectedList_congr (j : J) (S T : Finset (Sym2 V))
    (rs : List (Sym2 V × Finset J))
    (h : ∀ e∈rs.map Prod.fst,e∈S ↔ e∈T) : selectedList j S rs=selectedList j T rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨e,A⟩ := r
    have he := h e (by simp)
    have hh := ih (fun d hd => h d (List.mem_cons_of_mem e hd))
    simp only [selectedList,he,hh]

 theorem selectedList_insert_fresh (j : J) (S : Finset (Sym2 V))
    (rs : List (Sym2 V × Finset J)) {e : Sym2 V} (he : e∉rs.map Prod.fst) :
    selectedList j (insert e S) rs=selectedList j S rs := by
  apply selectedList_congr
  intro d hd
  have hde : d≠e := fun hh => he (hh ▸ hd)
  simp [hde]

omit [DecidableEq V] in
theorem ftCovered_zero (G : SimpleGraph V) (w : Sym2 V → ℝ) (t : ℝ) (e : Sym2 V) :
    FTCovered G w t 0 e ↔ Covered G w t e := by
  constructor
  · intro h
    simpa [afterFaults] using h ∅ (by simp) (by simp)
  · intro h F hF _
    have hzero : F=∅ := card_eq_zero.mp (Nat.le_zero.mp hF)
    simpa [hzero,afterFaults] using h

/-- The retained sampled greedy prefix is a literal subgraph of the larger
sampled execution prefix used by the estimator. -/
theorem selected_greedy_le_testSample (Q T S : Finset (Sym2 V))
    (w : Sym2 V → ℝ) (t : ℝ) (j : J) (rs : List (Sym2 V × Finset J))
    (hdis : ∀ e∈rs.map Prod.fst,e∉Q) :
    edgeGraph (greedyEdges T w t 0 (selectedList j S rs))≤
      testSample Q (Q∪(rs.map Prod.fst).toFinset) T S := by
  apply edgeGraph_mono
  intro e he
  rcases mem_union.mp (greedy_subset T w t 0 _ he) with he | he
  · exact mem_union_left _ he
  · have hl := List.mem_toFinset.mp he
    have hr := (selectedList_sublist j S rs).subset hl
    exact mem_union_right _ (mem_inter.mpr ⟨selectedList_mem_sample j S rs hl,
      mem_sdiff.mpr ⟨mem_union_right _ (List.mem_toFinset.mpr hr),hdis e hr⟩⟩)
end LightEFTSpanners.SampledGreedy
