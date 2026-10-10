import LightSpanners.LightnessBound
import LightSpanners.Construction
import LightSpanners.Counting

namespace LightSpanners
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual sorted greedy construction has near-optimal stretch and lightness.
Weights are nonnegative globally and strictly positive on graph edges. The
explicit constant baseline keeps the assertion valid for every positive epsilon. -/
theorem near_optimal_greedy_spanner (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hconn : G.Connected) (hw0 : ∀ e,0≤w e) (hw : ∀ e∈G.edgeSet,0<w e)
    {eps : ℝ} {k : ℕ} (heps : 0<eps) (hk : 0<k) :
    IsSpanner G (greedyOutput G w ((1+eps)*(2*k-1))) w ((1+eps)*(2*k-1)) ∧
    (∀ u v, weightedDistance (greedyOutput G w ((1+eps)*(2*k-1))) w u v≤
      ENNReal.ofReal ((1+eps)*(2*k-1))*weightedDistance G w u v) ∧
    ∃ T : SimpleGraph V, IsMinimumSpanningTree G T w ∧ T≤greedyOutput G w ((1+eps)*(2*k-1)) ∧
      lightness (greedyOutput G w ((1+eps)*(2*k-1))) T w≤
        8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹) := by
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hkpos : (0:ℝ)<k := by exact_mod_cast hk
  have hgap : 0≤eps*((k:ℝ)-1) := mul_nonneg heps.le (by linarith)
  let t : ℝ := (1+eps)*(2*k-1)
  have ht : 1≤t := by dsimp [t]; nlinarith [mul_pos heps hkpos]
  obtain ⟨hspan,hdist,hg,T,hTH,hT⟩ := greedyOutput_preliminaries G w t ht hw0 hconn
  refine ⟨hspan,hdist,T,hT,hTH,?_⟩
  have hTout : IsMinimumSpanningTree (greedyOutput G w t) T w :=
    ⟨hTH,hT.2.1,fun S hS htree => hT.2.2 S (hS.trans hspan.1) htree⟩
  have hterm : (0:ℝ)<2*k-1 := by linarith
  let δ : ℝ := eps*(2*k-1)/(8*k)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδlower : eps/8≤δ := by
    apply (le_div_iff₀ (by positivity : 0<(8:ℝ)*k)).mpr
    nlinarith [mul_pos heps hkpos]
  have hthreshold : (1+4*δ)*(2*k)=t+1 := stretch_reparameterization eps k hk
  have hG : WeightedGirthAbove (greedyOutput G w t) w ((1+4*δ)*(2*k)) := by
    rwa [hthreshold]
  have hb := weighted_girth_lightness_bound hTout
    (fun e he => hw e (edgeSet_mono hspan.1 he)) hδ hk hG
  have hcoef : 256/δ≤2048/eps := (div_le_div_iff₀ hδ heps).mpr (by nlinarith)
  have hm := mul_le_mul_of_nonneg_right hcoef
    (Real.rpow_nonneg (by positivity : (0:ℝ)≤Fintype.card V) ((k:ℝ)⁻¹))
  linarith

/-- Explicit fixed-epsilon form of Theorem 1.4: the coefficient is independent
of n and k, and the spanner is the actual greedy output. -/
theorem near_optimal_greedy_lightness (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hconn : G.Connected) (hw0 : ∀ e,0≤w e) (hw : ∀ e∈G.edgeSet,0<w e)
    {eps : ℝ} {k : ℕ} (heps : 0<eps) (hk : 0<k) :
    ∃ T : SimpleGraph V, IsMinimumSpanningTree G T w ∧
      lightness (greedyOutput G w ((1+eps)*(2*k-1))) T w≤
        (8+2048/eps)*(Fintype.card V:ℝ)^((k:ℝ)⁻¹) := by
  obtain ⟨_,_,T,hT,_,hbound⟩ := near_optimal_greedy_spanner G w hconn hw0 hw heps hk
  haveI := hconn.nonempty
  have hn : (1:ℝ)≤Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have hroot := Real.one_le_rpow hn (show (0:ℝ)≤(k:ℝ)⁻¹ by positivity)
  exact ⟨T,hT,by nlinarith⟩

end LightSpanners
