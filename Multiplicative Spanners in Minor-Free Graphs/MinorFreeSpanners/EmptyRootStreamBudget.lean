import MinorFreeSpanners.UnitTreeHeavyScaleBound
import MinorFreeSpanners.GeometricScaleBudget

/-! The complete finite prefix of auxiliary root injections is charged to the
actual unit spanning tree. Only the last processed band needs an edge witness;
earlier empty bands are included in the same bound. This supplies an accounting
bound, not the still separate construction of each injected phase. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem empty_root_stream_injections_le_tree {V : Type*} [Fintype V]
    {G T B : SimpleGraph V} {w : Sym2 V → ℝ} {g t u c : ℝ}
    (hT : T≤G) (hconn : T.Connected) (hunit : ∀ e∈T.edgeSet,w e=1)
    (hg : 2≤g) (hG : WeightedGirthAbove G w g)
    (hw : ∀ e∈G.edgeSet,0≤w e) (hB : B≤G)
    (ht : 2≤t) (hu : 0≤u) (hc : 0≤c) (n : ℕ)
    (hband : ∀ e∈B.edgeSet,(u*t^n)/2≤w e) (hne : B.edgeSet.Nonempty) :
    (∑ i∈range (n+1),10*c*(u*t^i))≤40*c*(T.edgeFinset.card:ℝ) := by
  have hlast := nonempty_band_scale_le_unit_budget hT hconn hunit hg hG hw hB hband hne
  have hsum := geometric_processed_mass_bound t u (T.edgeFinset.card:ℝ) ht hu
    (range (n+1)) n (Finset.Subset.refl _) hlast
  have hmul := mul_le_mul_of_nonneg_left hsum (show 0≤10*c by positivity)
  rw [←Finset.mul_sum]
  nlinarith only [hmul]

end MinorFreeSpanners
