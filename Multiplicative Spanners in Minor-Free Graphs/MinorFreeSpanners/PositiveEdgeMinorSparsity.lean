import MinorFreeSpanners.EdgeWeightTransport
import MinorFreeSpanners.GreedyMinorFreeSparsity

/-! The actual sparsity upper bound requires positive weights only on input
edges; no connectivity or graph-size restriction is needed. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners
attribute [local instance] Classical.propDecidable

 theorem positive_edge_minor_sparsity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (r h : ℕ)
    (hr : 1≤r) (hh : 0<h) (hw : ∀ e∈G.edgeSet,0<w e) (hfree : CliqueMinorFree G h) :
    ∃ H : SimpleGraph V, IsSpanner G H w (2*(r:ℝ)-1) ∧
      (H.edgeFinset.card:ℝ)≤(2*fullDensityLoss h*(h:ℝ)^(2/(r+1:ℝ)))*(Fintype.card V:ℝ) := by
  let z : Sym2 V → ℝ := fun e => if e∈G.edgeSet then w e else 1
  have hz : ∀ e,0<z e := by intro e; dsimp [z]; split_ifs with he; exact hw e he; norm_num
  have heq : ∀ e∈G.edgeSet,z e=w e := by intro e he; simp [z,he]
  obtain ⟨hspan,hsize⟩ := greedy_minor_free_sparsity G z r h hr hh hz hfree
  exact ⟨_,spanner_congr_edges heq hspan,hsize⟩

end MinorFreeSpanners
