import MinorFreeSpanners.ExplicitLightnessCoefficient

/-! Explicit polynomial inverse-slack and polylogarithmic minor-order factors
for the literal greedy spanner and its retained original minimum tree. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners
attribute [local instance] Classical.propDecidable
universe u

 theorem greedy_minor_polylog_lightness {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (eps : ℝ) (heps : 0<eps) (heps1 : eps≤1)
    (r h : ℕ) (hr : 1≤r) (hh : 3≤h)
    (hn : 2≤Fintype.card V) (hconn : G.Connected)
    (hfree : CliqueMinorFree G h) (hw : ∀ e,0<w e) :
    let stretch := (1+eps)*(2*(r:ℝ)-1)
    IsSpanner G (greedyOutput G w stretch) w stretch ∧
    CliqueMinorFree (greedyOutput G w stretch) h ∧
    ∃ T : SimpleGraph V, T≤greedyOutput G w stretch ∧ IsMinimumSpanningTree G T w ∧
      lightness (greedyOutput G w stretch) T w≤
        minorLightnessConstant*(Real.logb 2 (8097/eps)+1)*
          (Nat.log 2 h+2:ℕ)^9*(h:ℝ)^(2/(r+1:ℝ))/eps^3 := by
  intro stretch
  obtain ⟨hspan,hminor,T,hTH,hTG,hlight⟩ := greedy_minor_lightness G w eps heps heps1 r h hr hh hn hconn hfree hw
  exact ⟨hspan,hminor,T,hTH,hTG,hlight.trans (constructed_coefficient_bound eps heps heps1 r h (by omega))⟩

end MinorFreeSpanners
