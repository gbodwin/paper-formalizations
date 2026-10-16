import LightEFTSpanners.SpanningHostAssignments
import LightEFTSpanners.ConnectivityOptimum
import LightSpanners.CopyWeights

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners HostCounting
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
attribute [local instance] Classical.propDecidable

/-- The actual seeded recursion retains every actual seed edge. -/
theorem seed_le_output (G Q : SimpleGraph V) (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ) :
    Q ≤ output G Q w t f := by
  have hh := edgeGraph_mono (greedy_seed_subset Q.edgeFinset w t f (input G Q w))
  simpa only [edgeGraph,coe_edgeFinset,fromEdgeSet_edgeSet,output] using hh

/-- Algorithm 1 with a genuine optimum seed and a supplied spanning-tree
packing. The recursion, blocker map, assignments, sample, pruning and global
charging are proved. The existence of the supplied packing is an explicit
remaining premise, so this is not the unrestricted paper upper theorem. -/
theorem seeded_output_of_spanning_packing {G Q : SimpleGraph V} {w : Sym2 V → ℝ}
    {eps : ℝ} {f k h q : ℕ}
    (hQ : IsMinimumFTPreserver G Q w q)
    (indices : Finset I) (T : I → SimpleGraph V)
    (htrees : ∀ i∈indices, (T i).IsTree) (htreeQ : ∀ i∈indices, T i ≤ Q)
    (hcount : 2*f+h ≤ indices.card)
    (hcong : ∀ e∈Q.edgeFinset, (hosts indices (fun i => (T i).edgeFinset) e).card ≤ 2)
    (hw0 : ∀ e, 0≤w e) (hw : ∀ e∈G.edgeSet, 0<w e)
    (hf : 0<f) (hk : 0<k) (heps : 0<eps) (hn : 2≤Fintype.card V) (hh : 0<h) :
    IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1)) f) w ((1+eps)*(2*k-1)) f ∧
    competitiveLightness (output G Q w ((1+eps)*(2*k-1)) f) Q w ≤
      1+8*(f:ℝ)*(8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹))/h := by
  have hQG : Q≤G := hQ.1.1
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have ht : (1:ℝ)≤(1+eps)*(2*k-1) := by
    have hp := mul_nonneg heps.le (sub_nonneg.mpr hkR)
    nlinarith
  have hsp := output_isEFTSpanner G Q hQG w ((1+eps)*(2*k-1)) f ht hw0
  obtain ⟨i,hi⟩ := card_pos.mp (by omega : 0 < indices.card)
  have hTpos := tree_totalWeight_pos (htrees i hi) hn w
    (fun e he => hw e (edgeSet_mono ((htreeQ i hi).trans hQG) he))
  have hQpos : 0<totalWeight Q w := hTpos.trans_le
    (totalWeight_mono_subgraph (htreeQ i hi) w (fun e _ => hw0 e))
  obtain ⟨B,hB⟩ := output_has_blocking G Q hQG w ((1+eps)*(2*k-1)) f (by linarith)
  refine ⟨hsp,?_⟩
  exact spanning_packing_lightness (seed_le_output G Q w _ f) hQpos hB indices T
    htrees htreeQ hcount hcong (fun e he => hw e (edgeSet_mono hsp.1 he))
    hf hk heps hn hh
end LightEFTSpanners
