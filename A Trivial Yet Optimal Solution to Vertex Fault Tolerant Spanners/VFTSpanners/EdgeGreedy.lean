import VFTSpanners.EdgeFault

namespace VFTSpanners
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V]

/-- Algorithm 1, processing the list from right to left. A list in descending
weight order therefore processes edges in nondecreasing weight order. The
classical edge test is the exact mathematical test, not an efficient implementation. -/
noncomputable def edgeGreedyEdges (w : Sym2 V → ℝ) (k f : ℕ) :
    List (Sym2 V) → Finset (Sym2 V)
  | [] => ∅
  | e :: es => by
    classical
    exact let E := edgeGreedyEdges w k f es
      if EdgeCovered (edgeGraph E) w k f e then E else insert e E

theorem edgeGreedyEdges_subset (w : Sym2 V → ℝ) (k f : ℕ) (l : List (Sym2 V)) :
    edgeGreedyEdges w k f l ⊆ l.toFinset := by
  classical
  induction l with
  | nil => simp [edgeGreedyEdges]
  | cons e es ih =>
    simp only [edgeGreedyEdges]
    split_ifs
    · exact ih.trans (by simp)
    · exact insert_subset (by simp) (ih.trans (by simp))

theorem edgeGreedyEdges_covered (w : Sym2 V → ℝ) (k f : ℕ) (hk : 1 ≤ k)
    (hw : ∀ e, 0 ≤ w e) (l : List (Sym2 V)) (hl : ∀ e ∈ l, ¬ e.IsDiag) :
    ∀ e ∈ l, EdgeCovered (edgeGraph (edgeGreedyEdges w k f l)) w k f e := by
  classical
  induction l with
  | nil => simp
  | cons e es ih =>
    have hi := ih (fun d hd => hl d (by simp [hd]))
    intro d hd
    simp only [edgeGreedyEdges]
    split_ifs with hc
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact hc
      · exact hi d hd
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact edgeCovered_of_mem hk hw ((mem_edgeGraph _ _).mpr ⟨mem_insert_self _ _, hl d (by simp)⟩)
      · exact edgeCovered_mono (edgeGraph_mono (subset_insert _ _)) (hi d hd)

/-- Lemma 3 for the actual recursive greedy algorithm and any tie ordering. -/
theorem edgeGreedy_blocking (w : Sym2 V → ℝ) (k f : ℕ)
    (hw : ∀ e, 0 ≤ w e) (l : List (Sym2 V))
    (hnd : l.Nodup) (hs : l.Pairwise (fun e d => w d ≤ w e))
    (hl : ∀ e ∈ l, ¬ e.IsDiag) :
    ∃ B : Finset (V × Sym2 V),
      IsBlockingSet (edgeGraph (edgeGreedyEdges w k f l)) (k+1) (B : Set (V × Sym2 V)) ∧
      B.card ≤ f*(edgeGreedyEdges w k f l).card := by
  classical
  induction l with
  | nil =>
    refine ⟨∅,⟨by simp,?_⟩,by simp [edgeGreedyEdges]⟩
    intro a p hp
    cases p with
    | nil => exact (hp.ne_nil rfl).elim
    | cons h p => simp [edgeGreedyEdges,edgeGraph] at h
  | cons e es ih =>
    obtain ⟨hne,hnd⟩ := List.nodup_cons.mp hnd
    obtain ⟨hmax,hs⟩ := List.pairwise_cons.mp hs
    obtain ⟨B,hB,hcard⟩ := ih hnd hs (fun d hd => hl d (by simp [hd]))
    simp only [edgeGreedyEdges]
    split_ifs with hc
    · exact ⟨B,hB,hcard⟩
    · apply extend_blocking _ B w k f e (hl e (by simp)) _ (hw e) _ hB hcard (fun h => hc (covered_implies_edgeCovered h))
      · exact fun he => hne (List.mem_toFinset.mp (edgeGreedyEdges_subset w k f es he))
      · intro d hd
        exact hmax d (List.mem_toFinset.mp (edgeGreedyEdges_subset w k f es hd))

end VFTSpanners
