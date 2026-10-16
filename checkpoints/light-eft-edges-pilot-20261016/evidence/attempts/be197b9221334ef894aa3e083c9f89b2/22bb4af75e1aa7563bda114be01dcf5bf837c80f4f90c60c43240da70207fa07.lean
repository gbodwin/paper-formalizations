import LightSpanners.HikerTour
import LightSpanners.DyadicEnumeration

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {w : Sym2 V → ℝ} (C : UnitSpanningCycle G w)

/-- Lemma 5.8 for an actual finite graph. The bucket family is constructed
from all graph chords. The ambient extra-safe budget remains k, even when
more than k chords are produced. No girth assumption is needed here. -/
theorem exists_long_extra_safe_walk {eps : ℝ} {k : ℕ}
    (heps : 0 < eps) (hk : 0 < k)
    (hweight : 4*(Fintype.card V : ℝ) ≤ eps*(totalWeight G w-Fintype.card V)) :
    ∃ (u v : V) (p : G.Walk u v),
      (∃ J, C.BucketMonotoneWalk eps k true J p) ∧ k ≤ (C.chordEdges p).length := by
  obtain ⟨J,ds,hds,hd,hw,_hcover,hsum⟩ := C.exists_finite_dyadic_buckets
  obtain ⟨u,v,p,hp,hk'⟩ := WalkSquad.exists_long_bucket_tour C ds J
    (fun i _ => hds i) (fun i _ => hd i) (fun i _ => hw i) heps hk (by rwa [hsum])
  exact ⟨u,v,p,⟨J,hp⟩,hk'⟩

/-- Equivalent source-style weight threshold, with positive epsilon explicit. -/
theorem weak_counting {eps : ℝ} {k : ℕ}
    (heps : 0 < eps) (hk : 0 < k)
    (hweight : 4/eps*(Fintype.card V : ℝ) ≤ totalWeight G w-Fintype.card V) :
    ∃ (u v : V) (p : G.Walk u v),
      (∃ J, C.BucketMonotoneWalk eps k true J p) ∧ k ≤ (C.chordEdges p).length := by
  apply C.exists_long_extra_safe_walk heps hk
  have hm := mul_le_mul_of_nonneg_left hweight heps.le
  field_simp at hm
  nlinarith

end LightSpanners.UnitSpanningCycle
