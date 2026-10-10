import MinorFreeSpanners.ClusterGirth

namespace MinorFreeSpanners
open SimpleGraph LightSpanners
variable {I V : Type*} [DecidableEq V]
variable {A G B : SimpleGraph V} {w : Sym2 V → ℝ}

/-- Claim23's graph conclusion for an actual cluster family satisfying the
stated diameter and weight-scale invariants. It uses corrected Claim19 and
s≥4d. The existence of the multilevel hierarchy is a separate obligation. -/
theorem claim23_for_cluster_family (k h : ℕ) (d s ε ℓ : ℝ)
    (hk : 1 ≤ k) (hd : 0 ≤ d) (hs : 4*d ≤ s) (hε : 0 < ε) (hℓ : 0 < ℓ)
    (C : ClusterFamily (I := I) A w (d*ℓ)) (hA : A ≤ G) (hB : B ≤ G)
    (hminor : CliqueMinorFree G h)
    (hG : WeightedGirthAbove G w ((1+s*ε)*(2*k-1)+1))
    (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    (hlight : ∀ e ∈ A.edgeSet, w e < ℓ/(2*ε))
    (hheavy : ∀ e ∈ B.edgeSet, ℓ/(2*ε) ≤ w e) :
    CliqueMinorFree (C.graph B) h ∧ GirthAbove (C.graph B) (2*k) := by
  refine ⟨C.minorFree hA hB hminor,?_⟩
  apply C.girth hA hB (2*k) hG hw hlight hheavy
    (div_pos hℓ (mul_pos (by norm_num) hε)) (mul_nonneg hd hℓ.le)
  have hratio : d*ℓ/(ℓ/(2*ε)) = 2*d*ε := by field_simp [hε.ne',hℓ.ne']
  rw [hratio]
  have hb := cluster_threshold_repair k d s ε hk hd hs hε.le
  simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_comm] using hb

end MinorFreeSpanners
