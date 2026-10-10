import LightEFTSpanners.HostWeightTransport
import LightEFTSpanners.HostGraphSampling

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
attribute [local instance] Classical.propDecidable

/-- The per-host sampling/pruning proof applies to a genuine subtree vertex
set, rather than requiring the host to span all original vertices. All local
weights, seed edges and blockers are transported from the actual global graph. -/
theorem induced_host_candidate_weight_bound {G Q : SimpleGraph W}
    {T : SimpleGraph V} {w : Sym2 W → ℝ} {eps : ℝ} {f k : ℕ}
    {B : Sym2 W → Finset (Sym2 W)} (j : V ↪ W)
    (hQG : Q≤G) (hB : BlockingData G Q.edgeFinset w ((1+eps)*(2*k-1)) f B)
    (hT : T.IsTree) (hmapQ : T.map j≤Q) (U : Finset (Sym2 V))
    (hUG : ∀ e∈U, j.sym2Map e∈G.edgeSet)
    (hUQ : ∀ e∈U, j.sym2Map e∉Q.edgeFinset)
    (hhost : ∀ e∈U, Disjoint (B (j.sym2Map e)) (T.map j).edgeFinset)
    (hw : ∀ e∈G.edgeSet, 0<w e) (hf : 0<f) (hk : 0<k) (heps : 0<eps)
    (hn : 2≤Fintype.card V) :
    (∑ e∈U.map j.sym2Map,w e) ≤ 4*(f:ℝ)*
      (8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹))*totalWeight (T.map j) w := by
  have hTG : T≤G.comap j := map_le_iff_le_comap.mp (hmapQ.trans hQG)
  have hTQ : T≤Q.comap j := map_le_iff_le_comap.mp hmapQ
  have hseed : ∀ e∈T.edgeSet, e∈pullEdges j Q.edgeFinset := by
    intro e he
    apply (mem_pullEdges j _ e).mpr
    exact mem_edgeFinset.mpr ((mem_comap_edgeSet j Q e).mp (edgeSet_mono hTQ he))
  have hp := host_candidate_weight_bound (hB.comap j) hT hTG hseed
    (fun e he => (mem_comap_edgeSet j G e).mpr (hUG e he))
    (fun e he hd => hUQ e he ((mem_pullEdges j _ e).mp hd))
    (fun e he => (disjoint_pullEdges_host j _ T).mpr (hhost e he))
    (fun e he => hw _ ((mem_comap_edgeSet j G e).mp he)) hf hk heps hn
  rw [mapped_candidate_weight,totalWeight_map_embedding]
  exact hp

/-- The original vertex count bounds every induced host, including empty
candidate sets and singleton hosts. No hidden minimum host size is needed. -/
theorem induced_host_bound_in_global_order {G Q : SimpleGraph W}
    {T : SimpleGraph V} {w : Sym2 W → ℝ} {eps : ℝ} {f k : ℕ}
    {B : Sym2 W → Finset (Sym2 W)} (j : V ↪ W)
    (hQG : Q≤G) (hB : BlockingData G Q.edgeFinset w ((1+eps)*(2*k-1)) f B)
    (hT : T.IsTree) (hmapQ : T.map j≤Q) (U : Finset (Sym2 V))
    (hUG : ∀ e∈U, j.sym2Map e∈G.edgeSet)
    (hUQ : ∀ e∈U, j.sym2Map e∉Q.edgeFinset)
    (hhost : ∀ e∈U, Disjoint (B (j.sym2Map e)) (T.map j).edgeFinset)
    (hw : ∀ e∈G.edgeSet, 0<w e) (hf : 0<f) (hk : 0<k) (heps : 0<eps) :
    (∑ e∈U.map j.sym2Map,w e) ≤ 4*(f:ℝ)*
      (8+2048/eps*(Fintype.card W:ℝ)^((k:ℝ)⁻¹))*totalWeight (T.map j) w := by
  have hTw : 0≤totalWeight (T.map j) w := by
    unfold totalWeight
    apply sum_nonneg
    intro e he
    have he' : e ∈ (T.map j).edgeSet := by
      simpa only [mem_edgeFinset] using he
    exact (hw e (edgeSet_mono (hmapQ.trans hQG) he')).le
  by_cases hU : U.Nonempty
  · obtain ⟨e,he⟩ := hU
    obtain ⟨a,b⟩ := e
    have hab : a≠b := by
      intro h
      subst b
      have hh := hUG _ he
      exact G.loopless.irrefl (j a) hh
    have hnV : 2≤Fintype.card V := Nat.succ_le_iff.mpr
      (Fintype.one_lt_card_iff.mpr ⟨a,b,hab⟩)
    have hp := induced_host_candidate_weight_bound j hQG hB hT hmapQ U hUG hUQ
      hhost hw hf hk heps hnV
    have hcard : (Fintype.card V:ℝ)≤Fintype.card W := by
      exact_mod_cast Fintype.card_le_of_injective j j.injective
    have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (Fintype.card V)) hcard
      (by positivity : (0:ℝ)≤(k:ℝ)⁻¹)
    apply hp.trans
    apply mul_le_mul_of_nonneg_right _ hTw
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hm := mul_le_mul_of_nonneg_left hpow
      (show (0:ℝ) ≤ 2048/eps by positivity)
    linarith
  · have heq : U=∅ := not_nonempty_iff_eq_empty.mp hU
    simp only [heq,map_empty,sum_empty]
    positivity
end LightEFTSpanners
