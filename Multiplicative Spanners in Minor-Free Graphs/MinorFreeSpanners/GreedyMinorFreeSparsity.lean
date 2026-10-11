import MinorFreeSpanners.GirthMinorFreeUpper

/-! Actual greedy-spanner sparsity upper bound with an explicit degree-nine
polylogarithmic factor. The weighted-lightness hierarchy is separate. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners
attribute [local instance] Classical.propDecidable

theorem greedy_minor_free_sparsity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (r h : ℕ)
    (hr : 1≤r) (hh : 0<h) (hw : ∀ e, 0<w e) (hfree : CliqueMinorFree G h) :
    IsSpanner G (greedyOutput G w (2*r-1)) w (2*r-1) ∧
      ((greedyOutput G w (2*r-1)).edgeFinset.card:ℝ) ≤
        (2*fullDensityLoss h*(h:ℝ)^(2/(r+1:ℝ)))*(Fintype.card V:ℝ) := by
  have hrR : (1:ℝ)≤r := by exact_mod_cast hr
  obtain ⟨hminor,hgirth⟩ := claim15 G w r h hr hw hfree
  exact ⟨greedy_spanner G w (2*r-1) (by linarith) (fun e => (hw e).le),
    girth_minor_free_edge_bound _ r h hr hh hminor hgirth⟩

end MinorFreeSpanners
