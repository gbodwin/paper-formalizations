import VFTSpanners.ShortestPaths
import VFTSpanners.Padding

namespace VFTSpanners
open SimpleGraph
open scoped ENNReal
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Theorem 1, VFT setting. For every finite weighted input graph, the defined
Algorithm 1 output is a subgraph, preserves weighted distances after any at
most `f` vertex faults, and obeys the paper's size bound with explicit constant
36 and the integer argument `max 2 (floor(n/f))`. -/
theorem vft_greedy_theorem_one (G : SimpleGraph V) (w : Sym2 V → ℝ) (k f : ℕ)
    (hk : 1 ≤ k) (hf : 1 ≤ f) (hw : ∀ e, 0 ≤ w e) :
    greedyOutput G w k f ≤ G ∧
      (∀ F : Finset V, F.card ≤ f → ∀ u v,
        faultDistance (greedyOutput G w k f) w F u v ≤
          (k : ℝ≥0∞)*faultDistance G w F u v) ∧
      (greedyOutput G w k f).edgeFinset.card ≤
        36*f^2*extremalEdges (max 2 (Fintype.card V / f)) (k+1) := by
  obtain ⟨hs,hd,_⟩ := vft_greedy_distance_and_size G w k f hk hf hw
  obtain ⟨B,hB,hb⟩ := greedyOutput_blocking G w k f hw
  exact ⟨hs,hd,blocking_extremal_bound_paper _ B (k+1) f hf hB hb⟩

/-- The zero-fault case, which is excluded from the expression `n/f` in the
paper. Ordinary greedy has girth greater than `k+1` and at most `b(n,k+1)` edges. -/
theorem vft_greedy_zero_faults (G : SimpleGraph V) (w : Sym2 V → ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hw : ∀ e, 0 ≤ w e) :
    IsVFTSpanner G (greedyOutput G w k 0) w k 0 ∧
      HighGirth (greedyOutput G w k 0) (k+1) ∧
      (greedyOutput G w k 0).edgeFinset.card ≤ extremalEdges (Fintype.card V) (k+1) := by
  obtain ⟨B,hB,hb⟩ := greedyOutput_blocking G w k 0 hw
  have hBe : B = ∅ := Finset.card_eq_zero.mp (by simpa using hb)
  have hg : HighGirth (greedyOutput G w k 0) (k+1) := by
    intro a p hp
    by_contra hlen
    obtain ⟨x,e,hxe,_,_⟩ := hB.2 p hp (by omega)
    simp [hBe] at hxe
  exact ⟨greedy_isVFTSpanner G w k 0 hk hw,hg,
    edge_count_le_extremal _ _ _ rfl hg⟩

end VFTSpanners
