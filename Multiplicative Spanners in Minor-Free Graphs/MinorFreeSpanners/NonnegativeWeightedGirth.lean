import MinorFreeSpanners.Greedy

/-! Nonnegative weights suffice for the ordinary girth consequence. The
strict cycle inequality itself forces the maximal cycle edge to be positive. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners

 theorem weightedGirth_girth_nonnegative {V : Type*} {G : SimpleGraph V}
    {w : Sym2 V → ℝ} {r : ℕ} (hw : ∀ e∈G.edgeSet,0≤w e)
    (hg : WeightedGirthAbove G w r) : GirthAbove G r := by
  intro a p hp
  obtain ⟨e,he,hmax⟩ := exists_max_cycle_edge w p hp
  have hb := (hg a p hp e he).trans_le (walkWeight_le_length_mul p w (w e) hmax)
  have he0 := hw e (p.edges_subset_edgeSet he)
  have hep : 0<w e := by
    by_contra hn
    have hz : w e=0 := le_antisymm (le_of_not_gt hn) he0
    rw [hz,mul_zero,mul_zero] at hb
    exact (lt_irrefl 0) hb
  have hr : (r:ℝ)<p.length := (mul_lt_mul_iff_of_pos_right hep).mp hb
  exact_mod_cast hr

end MinorFreeSpanners
