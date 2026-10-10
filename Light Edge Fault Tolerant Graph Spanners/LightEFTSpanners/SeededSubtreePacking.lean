import LightEFTSpanners.SubtreeAssignments
import LightEFTSpanners.SeededSpanningPacking

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners HostCounting
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
variable {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
attribute [local instance] Classical.propDecidable

/-- The actual seeded greedy output, with a genuine optimum seed and supplied
subtree packing. The local vertex domains can differ. The zero-denominator case
is explicit, so neither graph nontriviality nor seed positivity is hidden.
The structural endpoint coverage/congestion packing remains a premise. -/
theorem seeded_output_of_subtree_packing {G Q : SimpleGraph V} {w : Sym2 V → ℝ}
    {eps : ℝ} {f k h q : ℕ} (hQ : IsMinimumFTPreserver G Q w q)
    (indices : Finset I) (j : ∀ i, A i ↪ V) (T : ∀ i, SimpleGraph (A i))
    (htrees : ∀ i∈indices, (T i).IsTree)
    (htreeQ : ∀ i∈indices, (T i).map (j i) ≤ Q)
    (hcount : ∀ e∈G.edgeFinset \ Q.edgeFinset,
      2*f+h ≤ (indices.filter (fun i => ∃ d, (j i).sym2Map d=e)).card)
    (hcong : ∀ e∈Q.edgeFinset,
      (hosts indices (fun i => ((T i).map (j i)).edgeFinset) e).card ≤ 2)
    (hw0 : ∀ e, 0≤w e) (hw : ∀ e∈G.edgeSet, 0<w e)
    (hf : 0<f) (hk : 0<k) (heps : 0<eps) (hh : 0<h) :
    IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1)) f) w ((1+eps)*(2*k-1)) f ∧
    competitiveLightness (output G Q w ((1+eps)*(2*k-1)) f) Q w ≤
      1+8*(f:ℝ)*(8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹))/h := by
  have hQG : Q≤G := hQ.1.1
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have ht : (1:ℝ)≤(1+eps)*(2*k-1) := by
    have hp := mul_nonneg heps.le (sub_nonneg.mpr hkR)
    nlinarith
  have hsp := output_isEFTSpanner G Q hQG w ((1+eps)*(2*k-1)) f ht hw0
  refine ⟨hsp,?_⟩
  by_cases hz : totalWeight Q w=0
  · simp only [competitiveLightness,hz,div_zero]
    positivity
  · have hQnn : 0≤totalWeight Q w := by
      unfold totalWeight
      exact sum_nonneg (fun e _ => hw0 e)
    have hQpos : 0<totalWeight Q w := lt_of_le_of_ne hQnn (Ne.symm hz)
    obtain ⟨B,hB⟩ := output_has_blocking G Q hQG w ((1+eps)*(2*k-1)) f (by linarith)
    apply subtree_packing_lightness (seed_le_output G Q w _ f) hQpos hB
      indices j T htrees htreeQ
    · intro e he
      exact hcount e (mem_sdiff.mpr ⟨edgeFinset_mono hsp.1 (mem_sdiff.mp he).1,
        (mem_sdiff.mp he).2⟩)
    · exact hcong
    · exact fun e he => hw e (edgeSet_mono hsp.1 he)
    · exact hf
    · exact hk
    · exact heps
    · exact hh
end LightEFTSpanners
