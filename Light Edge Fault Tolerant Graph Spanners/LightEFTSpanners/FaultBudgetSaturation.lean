import LightEFTSpanners.MissingEdgeConnectivity
import LightEFTSpanners.ConnectivityOptimum
import LightSpanners.Distance

/-! Exact finite saturation. These theorems do not assert an asymptotic
contradiction: that requires checking the source's uniformity and quantifier
order separately. -/
namespace LightEFTSpanners
open SimpleGraph LightSpanners
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

/-- A simple n-vertex graph has no proper q-fault connectivity preserver once
q≥n−2. This finite statement includes disconnected graphs. -/
theorem preserver_eq_at_large_budget {G Q : SimpleGraph V} {q : ℕ}
    (hQ : IsFTConnectivityPreserver G Q q) (hn : Fintype.card V ≤ q+2) : Q=G := by
  apply preserver_eq_of_degree_le hQ
  intro u
  have hd := G.degree_lt_card_verts u
  omega

/-- The original graph is always an eligible spanner at stretch at least one. -/
theorem self_eftSpanner (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e,0≤w e) {t : ℝ} (ht : 1≤t) (f : ℕ) : IsEFTSpanner G G w t f := by
  refine ⟨le_rfl,fun F _ => ⟨le_rfl,?_⟩⟩
  intro u v p
  refine ⟨p,?_⟩
  have hp := walkWeight_nonneg w hw p
  nlinarith

/-- Any true optimal denominator equals G at saturation. The self spanner has
competitive ratio at most one, including the zero-total-weight convention. -/
theorem saturated_competitive_self {G Q : SimpleGraph V} {q : ℕ}
    {w : Sym2 V → ℝ} (hQ : IsMinimumFTPreserver G Q w q)
    (hn : Fintype.card V ≤ q+2) : competitiveLightness G Q w ≤ 1 := by
  rw [preserver_eq_at_large_budget hQ.1 hn]
  unfold competitiveLightness
  exact div_self_le_one _

/-- Exact finite saturation obstructs any jointly uniform lower claim that
demands a ratio greater than one, regardless of how its graph is constructed. -/
theorem exists_saturated_eligible_output (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e,0≤w e) (q f : ℕ) (hn : Fintype.card V ≤ q+2)
    {t : ℝ} (ht : 1≤t) :
    ∃ H Q : SimpleGraph V, IsEFTSpanner G H w t f ∧
      IsMinimumFTPreserver G Q w q ∧ competitiveLightness H Q w ≤ 1 := by
  obtain ⟨Q,hQ⟩ := exists_minimum_preserver G w q
  exact ⟨G,Q,self_eftSpanner G w hw ht f,hQ,saturated_competitive_self hQ hn⟩
end LightEFTSpanners
