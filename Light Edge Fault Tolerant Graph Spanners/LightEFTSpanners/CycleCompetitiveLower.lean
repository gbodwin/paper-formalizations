import LightEFTSpanners.CycleCoreRetention
import LightEFTSpanners.CoreGraphWeight
import LightEFTSpanners.CycleCertificate
import LightEFTSpanners.SubdivisionWeight
import LightEFTSpanners.ConnectivityOptimum

namespace LightEFTSpanners.ParallelSubdivision
open SimpleGraph Finset LightSpanners
attribute [local instance] Classical.propDecidable

/-- A proof-only common enumeration for the same actual finite edge sum. -/
private noncomputable def canonicalWeight {X : Type*} [Finite X]
    (G : SimpleGraph X) (w : Sym2 X → ℝ) : ℝ :=
  @totalWeight X (Fintype.ofFinite X) G w

private theorem totalWeight_canonical {X : Type*} [i : Fintype X]
    (G : SimpleGraph X) (w : Sym2 X → ℝ) : totalWeight G w=canonicalWeight G w := by
  unfold canonicalWeight
  exact congrArg (fun j : Fintype X => @totalWeight X j G w)
    (Subsingleton.elim i (Fintype.ofFinite X))

/-- Cardinality is independent of the local finite-edge enumeration. -/
theorem cycle_edge_count_at (m : ℕ) (i : Fintype (cycleGraph (m+3)).edgeSet) :
    (@SimpleGraph.edgeFinset (Fin (m+3)) (cycleGraph (m+3)) i).card=m+3 := by
  rw [edgeFinset_card,← Nat.card_eq_fintype_card]
  simpa only [edgeFinset_card,← Nat.card_eq_fintype_card] using cycle_base_edge_count m

theorem cycle_preserver_weight_pos (m f q : ℕ) {W : ℝ} (hW : 2≤W)
    {Q : SimpleGraph (Vertex (I:=Fin f) (cycleGraph (m+3)))}
    (hQ : IsFTConnectivityPreserver
      (graph (cycleGraph (m+3)) ⊔ coreGraph (cycleGraph (m+3)) (cycleGraph (m+3))) Q q) :
    0<totalWeight Q (coreWeight (cycleGraph (m+3)) W) := by
  classical
  have hadj : (cycleGraph (m+3)).Adj 0 1 := by rw [cycleGraph_adj]; exact Or.inr (by simp)
  have hnonempty : Q.edgeFinset.Nonempty := by
    rw [edgeFinset_nonempty]
    intro heq
    have hr := (hQ.2 ∅ (by simp) (Sum.inl 0) (Sum.inl 1)).mp
      (by simpa [afterFaults] using (show
        (graph (cycleGraph (m+3)) ⊔ coreGraph (cycleGraph (m+3)) (cycleGraph (m+3))).Adj
        (Sum.inl 0) (Sum.inl 1) from Or.inr hadj).reachable)
    have hne : (0:Fin (m+3))≠1 := hadj.ne
    simp [afterFaults,heq,reachable_bot,hne] at hr
  have hp : (0:ℝ)<Q.edgeFinset.card := by exact_mod_cast card_pos.mpr hnonempty
  have hb := card_mul_le_totalWeight Q (coreWeight (cycleGraph (m+3)) W) 1
    (by intro e _; unfold coreWeight; split_ifs <;> linarith)
  exact hp.trans_le (by simpa only [mul_one] using hb)

/-- A quantitative lower bound against the genuine minimum q-fault
preserver, for every q≤2f−1, derived from the actual unit certificate and forced core edges. -/
theorem cycle_competitive_lower (m f q : ℕ) (hf : 0<f) (hq : q≤2*f-1) (W t : ℝ)
    (hW : 2≤W) (hgap : t*W<2*(m+2))
    {H Q : SimpleGraph (Vertex (I:=Fin f) (cycleGraph (m+3)))}
    (hH : IsEFTSpanner
      (graph (cycleGraph (m+3)) ⊔ coreGraph (cycleGraph (m+3)) (cycleGraph (m+3)))
      H (coreWeight (cycleGraph (m+3)) W) t f)
    (hQ : IsMinimumFTPreserver
      (graph (cycleGraph (m+3)) ⊔ coreGraph (cycleGraph (m+3)) (cycleGraph (m+3)))
      Q (coreWeight (cycleGraph (m+3)) W) q) :
    W/(2*f)≤competitiveLightness H Q (coreWeight (cycleGraph (m+3)) W) := by
  classical
  have hret : coreGraph (I:=Fin f) (cycleGraph (m+3)) (cycleGraph (m+3))≤H :=
    cycle_core_retained m f W t hW hgap H hH
  have hn := core_retention_weight (I:=Fin f) (cycleGraph (m+3)) (W:=W) (H:=H)
    (by linarith : 0≤W) hret
  rw [cycle_edge_count_at] at hn
  have hc := (cycle_unit_graph_isFTPreserver m f hf (cycleGraph (m+3))).fault_mono hq
  have hunit := unit_weight_bound (I:=Fin f) (cycleGraph (m+3))
    (coreWeight (I:=Fin f) (cycleGraph (m+3)) W)
    (fun e he => coreWeight_unit (I:=Fin f) (cycleGraph (m+3)) W he)
  have hmin := hQ.2 (graph (I:=Fin f) (cycleGraph (m+3))) hc
  simp only [totalWeight_canonical] at hn hunit hmin
  have hd := hmin.trans hunit
  rw [cycle_edge_count_at] at hd
  simp only [Fintype.card_fin] at hd
  have hp := cycle_preserver_weight_pos m f q hW hQ.1
  have hfR : (0:ℝ)<f := by exact_mod_cast hf
  unfold competitiveLightness
  simp only [totalWeight_canonical] at hp ⊢
  apply (le_div_iff₀ hp).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2*f)).mpr
  have hb := mul_le_mul_of_nonneg_left hd (by linarith : 0≤W)
  have hn' := mul_le_mul_of_nonneg_right hn (by positivity : (0:ℝ)≤2*f)
  nlinarith only [hb,hn']
end LightEFTSpanners.ParallelSubdivision
