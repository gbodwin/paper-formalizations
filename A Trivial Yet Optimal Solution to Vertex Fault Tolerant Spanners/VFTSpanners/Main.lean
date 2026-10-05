import VFTSpanners.Greedy
import VFTSpanners.Extremal

namespace VFTSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- A weight-sorted enumeration of the input edges, largest weights first.
The algorithm processes this list from its tail. -/
noncomputable def greedyInput (G : SimpleGraph V) (w : Sym2 V → ℝ) : List (Sym2 V) :=
  G.edgeFinset.toList.mergeSort (fun e d => decide (w d ≤ w e))

omit [DecidableEq V] in
theorem greedyInput_perm (G : SimpleGraph V) (w : Sym2 V → ℝ) :
    (greedyInput G w).Perm G.edgeFinset.toList := List.mergeSort_perm _ _

omit [DecidableEq V] in
@[simp] theorem mem_greedyInput (G : SimpleGraph V) (w : Sym2 V → ℝ) (e : Sym2 V) :
    e ∈ greedyInput G w ↔ e ∈ G.edgeFinset := by
  rw [(greedyInput_perm G w).mem_iff, mem_toList]

omit [DecidableEq V] in
theorem greedyInput_sorted (G : SimpleGraph V) (w : Sym2 V → ℝ) :
    (greedyInput G w).Pairwise (fun e d => w d ≤ w e) := by
  have h := List.pairwise_mergeSort
    (le := fun e d : Sym2 V => decide (w d ≤ w e))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; exact hbc.trans hab)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) G.edgeFinset.toList
  simpa only [greedyInput, decide_eq_true_eq] using h

/-- The weighted VFT greedy output graph. -/
noncomputable def greedyOutput (G : SimpleGraph V) (w : Sym2 V → ℝ) (k f : ℕ) :
    SimpleGraph V := edgeGraph (greedyEdges w k f (greedyInput G w))

theorem greedyOutput_subgraph (G : SimpleGraph V) (w : Sym2 V → ℝ) (k f : ℕ) :
    greedyOutput G w k f ≤ G := by
  apply edgeSet_subset_edgeSet.mp
  intro e he
  have h := greedyEdges_subset w k f (greedyInput G w) ((mem_edgeGraph _ _).mp he).1
  exact mem_edgeFinset.mp ((mem_greedyInput G w e).mp (List.mem_toFinset.mp h))

theorem greedyOutput_edgeFinset (G : SimpleGraph V) (w : Sym2 V → ℝ) (k f : ℕ) :
    (greedyOutput G w k f).edgeFinset = greedyEdges w k f (greedyInput G w) := by
  ext e
  constructor
  · intro he
    exact ((mem_edgeGraph _ _).mp (SimpleGraph.mem_edgeFinset.mp he)).1
  intro he
  apply SimpleGraph.mem_edgeFinset.mpr
  apply (mem_edgeGraph _ _).mpr
  refine ⟨he,?_⟩
  have h := greedyEdges_subset w k f (greedyInput G w) he
  exact G.not_isDiag_of_mem_edgeFinset ((mem_greedyInput G w e).mp (List.mem_toFinset.mp h))

/-- Correctness of Algorithm 1, including arbitrary nonnegative real weights. -/
theorem greedy_isVFTSpanner (G : SimpleGraph V) (w : Sym2 V → ℝ) (k f : ℕ)
    (hk : 1 ≤ k) (hw : ∀ e, 0 ≤ w e) :
    IsVFTSpanner G (greedyOutput G w k f) w k f := by
  apply covered_edges_spanner (greedyOutput_subgraph G w k f)
  intro e he
  apply greedyEdges_covered w k f hk hw (greedyInput G w)
  · intro d hd
    exact G.not_isDiag_of_mem_edgeFinset ((mem_greedyInput G w d).mp hd)
  · exact (mem_greedyInput G w e).mpr (mem_edgeFinset.mpr he)

/-- Lemma 3 specialized to the sorted algorithm on an arbitrary input graph. -/
theorem greedyOutput_blocking (G : SimpleGraph V) (w : Sym2 V → ℝ) (k f : ℕ)
    (hw : ∀ e, 0 ≤ w e) :
    ∃ B : Finset (V × Sym2 V),
      IsBlockingSet (greedyOutput G w k f) (k+1) (B : Set (V × Sym2 V)) ∧
      B.card ≤ f*(greedyOutput G w k f).edgeFinset.card := by
  rw [greedyOutput_edgeFinset]
  exact greedy_blocking w k f hw (greedyInput G w)
    ((greedyInput_perm G w).nodup_iff.mpr G.edgeFinset.nodup_toList)
    (greedyInput_sorted G w)
    (fun e he => G.not_isDiag_of_mem_edgeFinset ((mem_greedyInput G w e).mp he))

/-- End-to-end VFT main theorem: the defined greedy algorithm returns a
fault-tolerant weighted spanner and satisfies an explicit finite version of
Theorem 1. No blocking-set or high-girth-subgraph hypothesis is assumed. -/
theorem vft_greedy_main (G : SimpleGraph V) (w : Sym2 V → ℝ) (k f : ℕ)
    (hk : 1 ≤ k) (hf : 1 ≤ f) (hw : ∀ e, 0 ≤ w e) :
    IsVFTSpanner G (greedyOutput G w k f) w k f ∧
      (greedyOutput G w k f).edgeFinset.card ≤
        36*f^2 * extremalEdges (max 2 (Fintype.card V / (2*f))) (k+1) := by
  obtain ⟨B,hB,hb⟩ := greedyOutput_blocking G w k f hw
  exact ⟨greedy_isVFTSpanner G w k f hk hw,
    blocking_extremal_bound _ B (k+1) f hf hB hb⟩

end VFTSpanners
