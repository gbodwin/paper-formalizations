import VFTSpanners.EdgeGreedy
import VFTSpanners.Corollary

namespace VFTSpanners
open SimpleGraph Finset
open scoped ENNReal
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- The weighted EFT greedy output graph. -/
noncomputable def edgeGreedyOutput (G : SimpleGraph V) (w : Sym2 V → ℝ) (k f : ℕ) :
    SimpleGraph V := edgeGraph (edgeGreedyEdges w k f (greedyInput G w))

theorem edgeGreedyOutput_subgraph (G : SimpleGraph V) (w : Sym2 V → ℝ) (k f : ℕ) :
    edgeGreedyOutput G w k f ≤ G := by
  apply edgeSet_subset_edgeSet.mp
  intro e he
  have h := edgeGreedyEdges_subset w k f (greedyInput G w) ((mem_edgeGraph _ _).mp he).1
  exact mem_edgeFinset.mp ((mem_greedyInput G w e).mp (List.mem_toFinset.mp h))

theorem edgeGreedyOutput_edgeFinset (G : SimpleGraph V) (w : Sym2 V → ℝ) (k f : ℕ) :
    (edgeGreedyOutput G w k f).edgeFinset = edgeGreedyEdges w k f (greedyInput G w) := by
  ext e
  constructor
  · intro he
    exact ((mem_edgeGraph _ _).mp (SimpleGraph.mem_edgeFinset.mp he)).1
  intro he
  apply SimpleGraph.mem_edgeFinset.mpr
  apply (mem_edgeGraph _ _).mpr
  refine ⟨he,?_⟩
  have h := edgeGreedyEdges_subset w k f (greedyInput G w) he
  exact G.not_isDiag_of_mem_edgeFinset ((mem_greedyInput G w e).mp (List.mem_toFinset.mp h))

/-- Correctness of Algorithm 1, including arbitrary nonnegative real weights. -/
theorem greedy_isEFTSpanner (G : SimpleGraph V) (w : Sym2 V → ℝ) (k f : ℕ)
    (hk : 1 ≤ k) (hw : ∀ e, 0 ≤ w e) :
    IsEFTSpanner G (edgeGreedyOutput G w k f) w k f := by
  apply edgeCovered_edges_spanner (edgeGreedyOutput_subgraph G w k f)
  intro e he
  apply edgeGreedyEdges_covered w k f hk hw (greedyInput G w)
  · intro d hd
    exact G.not_isDiag_of_mem_edgeFinset ((mem_greedyInput G w d).mp hd)
  · exact (mem_greedyInput G w e).mpr (mem_edgeFinset.mpr he)

/-- Lemma 3 specialized to the sorted algorithm on an arbitrary input graph. -/
theorem edgeGreedyOutput_blocking (G : SimpleGraph V) (w : Sym2 V → ℝ) (k f : ℕ)
    (hw : ∀ e, 0 ≤ w e) :
    ∃ B : Finset (V × Sym2 V),
      IsBlockingSet (edgeGreedyOutput G w k f) (k+1) (B : Set (V × Sym2 V)) ∧
      B.card ≤ f*(edgeGreedyOutput G w k f).edgeFinset.card := by
  rw [edgeGreedyOutput_edgeFinset]
  exact edgeGreedy_blocking w k f hw (greedyInput G w)
    ((greedyInput_perm G w).nodup_iff.mpr G.edgeFinset.nodup_toList)
    (greedyInput_sorted G w)
    (fun e he => G.not_isDiag_of_mem_edgeFinset ((mem_greedyInput G w e).mp he))

/-- End-to-end EFT main theorem: the defined greedy algorithm returns a
fault-tolerant weighted spanner and satisfies an explicit finite version of
Theorem 1. No blocking-set or high-girth-subgraph hypothesis is assumed. -/
theorem eft_greedy_main (G : SimpleGraph V) (w : Sym2 V → ℝ) (k f : ℕ)
    (hk : 1 ≤ k) (hf : 1 ≤ f) (hw : ∀ e, 0 ≤ w e) :
    IsEFTSpanner G (edgeGreedyOutput G w k f) w k f ∧
      (edgeGreedyOutput G w k f).edgeFinset.card ≤
        36*f^2 * extremalEdges (max 2 (Fintype.card V / (2*f))) (k+1) := by
  obtain ⟨B,hB,hb⟩ := edgeGreedyOutput_blocking G w k f hw
  exact ⟨greedy_isEFTSpanner G w k f hk hw,
    blocking_extremal_bound _ B (k+1) f hf hB hb⟩

/-- Theorem 1 in the EFT setting, for the actual weighted edge-fault greedy algorithm. -/
theorem eft_greedy_theorem_one (G : SimpleGraph V) (w : Sym2 V → ℝ) (k f : ℕ)
    (hk : 1 ≤ k) (hf : 1 ≤ f) (hw : ∀ e, 0 ≤ w e) :
    edgeGreedyOutput G w k f ≤ G ∧
      (∀ F : Finset (Sym2 V), F.card ≤ f → ∀ u v,
        edgeFaultDistance (edgeGreedyOutput G w k f) w F u v ≤
          (k : ℝ≥0∞)*edgeFaultDistance G w F u v) ∧
      (edgeGreedyOutput G w k f).edgeFinset.card ≤
        36*f^2*extremalEdges (max 2 (Fintype.card V / f)) (k+1) := by
  have hspan := greedy_isEFTSpanner G w k f hk hw
  obtain ⟨B,hB,hb⟩ := edgeGreedyOutput_blocking G w k f hw
  exact ⟨hspan.1,fun F hF u v => hspan.distance_le hk F hF u v,
    blocking_extremal_bound_paper _ B (k+1) f hf hB hb⟩

/-- Corollary 2 conditional on an explicit Moore bound, in equivalent
integer-power form: `m^r ≤ (36 C)^r n^(r+1) f^(r-1)` for stretch `2r-1`.
This modular version accepts any proved constant `C`; `eft_corollary_two` below
discharges the premise with `C = 2`. -/
theorem eft_corollary_two_from_moore {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (r f C : ℕ)
    (hr : 1 ≤ r) (hf : 1 ≤ f) (hC : 1 ≤ C) (hw : ∀ e, 0 ≤ w e)
    (hMoore : MooreBound r C) :
    (edgeGreedyOutput G w (2*r-1) f).edgeFinset.card^r ≤
      (36*C)^r*(Fintype.card V)^(r+1)*f^(r-1) := by
  by_cases hn : 2*f ≤ Fintype.card V
  · obtain ⟨_,_,hsize⟩ := eft_greedy_theorem_one G w (2*r-1) f (by omega) hf hw
    have heq : 2*r-1+1 = 2*r := by omega
    rw [heq] at hsize
    exact moore_substitution _ _ _ _ _ hf hr hn hMoore hsize
  · apply dense_fault_power_bound _ _ _ _ _ hr hC (by omega)
    have hc := (edgeGreedyOutput G w (2*r-1) f).card_edgeFinset_le_card_choose_two
    rw [Nat.choose_two_right] at hc
    have hd := Nat.div_le_self (Fintype.card V * (Fintype.card V - 1)) 2
    have hp := Nat.mul_le_mul_left (Fintype.card V) (Nat.sub_le (Fintype.card V) 1)
    nlinarith

/-- Unconditional size bound in Corollary 2, with uniform constant `72`. -/
theorem eft_corollary_two_size {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (r f : ℕ)
    (hr : 1 ≤ r) (hf : 1 ≤ f) (hw : ∀ e, 0 ≤ w e) :
    (edgeGreedyOutput G w (2*r-1) f).edgeFinset.card^r ≤
      72^r*(Fintype.card V)^(r+1)*f^(r-1) := by
  simpa using eft_corollary_two_from_moore G w r f 2 hr hf (by omega) hw
    (mooreBound_two r hr)

/-- Corollary 2, EFT setting, with no assumed extremal bound. The actual
weighted greedy output is a subgraph, preserves all surviving distances
within stretch `2*r-1` after at most `f` edge faults, and satisfies the
paper's size bound in integer-power form. -/
theorem eft_corollary_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (r f : ℕ)
    (hr : 1 ≤ r) (hf : 1 ≤ f) (hw : ∀ e, 0 ≤ w e) :
    edgeGreedyOutput G w (2*r-1) f ≤ G ∧
      (∀ F : Finset (Sym2 V), F.card ≤ f → ∀ u v,
        edgeFaultDistance (edgeGreedyOutput G w (2*r-1) f) w F u v ≤
          ((2*r-1 : ℕ) : ℝ≥0∞)*edgeFaultDistance G w F u v) ∧
      (edgeGreedyOutput G w (2*r-1) f).edgeFinset.card^r ≤
        72^r*(Fintype.card V)^(r+1)*f^(r-1) := by
  obtain ⟨hs,hd,_⟩ := eft_greedy_theorem_one G w (2*r-1) f (by omega) hf hw
  exact ⟨hs,hd,eft_corollary_two_size G w r f hr hf hw⟩

end VFTSpanners
