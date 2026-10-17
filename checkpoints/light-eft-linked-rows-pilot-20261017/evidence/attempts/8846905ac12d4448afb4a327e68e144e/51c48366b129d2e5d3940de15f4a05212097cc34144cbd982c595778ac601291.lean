import LightEFTSpanners.SubdivisionForcing
import LightEFTSpanners.CycleRotatedPotential

namespace LightEFTSpanners.ParallelSubdivision
open SimpleGraph
attribute [local instance] Classical.propDecidable

/-- Every heavy core edge of the actual cycle construction is forced by its
own explicitly rotated potential and its own f-edge failure set. -/
theorem cycle_core_retained (m f : ℕ) (W t : ℝ) (hW : 2≤W)
    (hgap : t*W<2*(m+2))
    (H : SimpleGraph (Vertex (I:=Fin f) (cycleGraph (m+3))))
    (hH : IsEFTSpanner
      (graph (cycleGraph (m+3)) ⊔ coreGraph (cycleGraph (m+3)) (cycleGraph (m+3)))
      H (coreWeight (cycleGraph (m+3)) W) t f) :
    coreGraph (cycleGraph (m+3)) (cycleGraph (m+3))≤H := by
  classical
  have hpred (r : Fin (m+3)) : H.Adj (Sum.inl r) (Sum.inl (r-1)) := by
    have hadj : (cycleGraph (m+3)).Adj r (r-1) := by
      rw [cycleGraph_adj]
      left
      abel
    apply core_edge_forced (cycleGraph (m+3)) hadj W t hW (cyclePotential m r)
    · exact cyclePotential_lipschitz m r
    · rw [cyclePotential_gap]
      exact hgap
    · simpa only [Fintype.card_fin] using hH
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change (cycleGraph (m+3)).Adj a b at hab
      rcases cycleGraph_adj.mp hab with hab | hab
      · have hb : b=a-1 := by
          have he := sub_eq_iff_eq_add.mp hab
          rw [he]
          abel
        simpa only [hb] using hpred a
      · have ha : a=b-1 := by
          have he := sub_eq_iff_eq_add.mp hab
          rw [he]
          abel
        simpa only [ha] using (hpred b).symm
    | inr b => exact False.elim hab
  | inr a => cases b <;> exact False.elim hab
end LightEFTSpanners.ParallelSubdivision
