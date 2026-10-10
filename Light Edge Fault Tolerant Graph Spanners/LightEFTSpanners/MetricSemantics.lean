import LightEFTSpanners.Basic
import LightSpanners.Distance

namespace LightEFTSpanners
open SimpleGraph LightSpanners
variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Equivalence with the paper's literal all-pairs weighted-distance inequality.
Infinite distances are handled in ENNReal, and t>0 rules out 0*infinity. -/
theorem eftSpanner_iff_distance (G H : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (t : ℝ) (ht : 0 < t) (f : ℕ) :
    IsEFTSpanner G H w t f ↔ H ≤ G ∧
      ∀ F : Finset (Sym2 V), F.card ≤ f → ∀ u v,
        weightedDistance (afterFaults H F) w u v ≤
          ENNReal.ofReal t * weightedDistance (afterFaults G F) w u v := by
  constructor
  · rintro ⟨hsub,h⟩
    exact ⟨hsub,fun F hF => ((isSpanner_iff_distance _ _ w hw t ht).mp (h F hF)).2⟩
  · rintro ⟨hsub,h⟩
    exact ⟨hsub,fun F hF => (isSpanner_iff_distance _ _ w hw t ht).mpr
      ⟨afterFaults_mono hsub F,h F hF⟩⟩

end LightEFTSpanners
