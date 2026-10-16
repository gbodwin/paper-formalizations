import LightEFTSpanners.HostGraphSampling
import LightEFTSpanners.HostCounting

/-! A conditional, concrete spanning-host-family assembly. The supplied tree
family and candidate assignments are explicit finite graphs/sets; their
existence is NOT asserted or encoded as the desired final inequality. -/
namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners HostCounting
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
attribute [local instance] Classical.propDecidable

/-- Concrete coverage and edge congestion imply the baseline-retaining coarse
lightness bound. Every host must span this fixed vertex set. General forest
components and the global host-family existence remain separate obligations. -/
theorem spanning_host_family_bound {G Q : SimpleGraph V} {w : Sym2 V → ℝ}
    {eps : ℝ} {f k h : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hQG : Q≤G) (hQpos : 0<totalWeight Q w)
    (hB : BlockingData G Q.edgeFinset w ((1+eps)*(2*k-1)) f B)
    (indices : Finset I) (T : I → SimpleGraph V) (U : I → Finset (Sym2 V))
    (htrees : ∀ i∈indices,(T i).IsTree) (htreeQ : ∀ i∈indices,T i≤Q)
    (hUG : ∀ i∈indices,∀ e∈U i,e∈G.edgeSet)
    (hUQ : ∀ i∈indices,∀ e∈U i,e∉Q.edgeFinset)
    (hhost : ∀ i∈indices,∀ e∈U i,Disjoint (B e) (T i).edgeFinset)
    (hcover : ∀ e∈G.edgeFinset \ Q.edgeFinset,h≤(hosts indices U e).card)
    (hcong : ∀ e∈Q.edgeFinset,(hosts indices (fun i => (T i).edgeFinset) e).card≤2)
    (hw : ∀ e∈G.edgeSet,0<w e) (hf : 0<f) (hk : 0<k) (heps : 0<eps)
    (hn : 2≤Fintype.card V) (hh : 0<h) :
    totalWeight G w / totalWeight Q w ≤
      1+8*(f:ℝ)*(8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹))/h := by
  classical
  let E := G.edgeFinset \ Q.edgeFinset
  let L : ℝ := 8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹)
  have hL : 0≤L := by dsimp [L]; positivity
  have hsub : ∀ i∈indices,U i⊆E := by
    intro i hi e he
    exact mem_sdiff.mpr ⟨mem_edgeFinset.mpr (hUG i hi e he),hUQ i hi e he⟩
  have hinc := weighted_incidence indices E U w hsub
  have hmult : (h:ℝ)*(∑ e∈E,w e) ≤ ∑ i∈indices,∑ e∈U i,w e := by
    rw [hinc,mul_sum]
    apply sum_le_sum
    intro e he
    have hh' : (h:ℝ)≤(hosts indices U e).card := by exact_mod_cast hcover e he
    exact mul_le_mul_of_nonneg_right hh' (hw e (mem_edgeFinset.mp (mem_sdiff.mp he).1)).le
  have hper : (∑ i∈indices,∑ e∈U i,w e) ≤
      4*(f:ℝ)*L*(∑ i∈indices,totalWeight (T i) w) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    exact host_candidate_weight_bound hB (htrees i hi) ((htreeQ i hi).trans hQG)
      (fun e he => mem_edgeFinset.mpr (edgeSet_mono (htreeQ i hi) he))
      (hUG i hi) (hUQ i hi) (hhost i hi) hw hf hk heps hn
  have htreeSub : ∀ i∈indices,(T i).edgeFinset⊆Q.edgeFinset := by
    intro i hi
    exact edgeFinset_mono (htreeQ i hi)
  have htinc := weighted_incidence indices Q.edgeFinset (fun i => (T i).edgeFinset) w htreeSub
  have htw : (∑ i∈indices,totalWeight (T i) w)≤2*totalWeight Q w := by
    unfold totalWeight
    rw [htinc,mul_sum]
    apply sum_le_sum
    intro e he
    have hc : ((hosts indices (fun i => (T i).edgeFinset) e).card:ℝ)≤2 := by
      exact_mod_cast hcong e he
    exact mul_le_mul_of_nonneg_right hc (hw e (edgeSet_mono hQG (mem_edgeFinset.mp he))).le
  have hadd : 0≤∑ e∈E,w e := sum_nonneg (fun e he =>
    (hw e (mem_edgeFinset.mp (mem_sdiff.mp he).1)).le)
  have hb := baseline_charging hQpos hh hadd hL hmult hper htw
  have hweight : totalWeight G w=totalWeight Q w+∑ e∈E,w e := by
    unfold totalWeight
    have hs := sum_sdiff (f:=w) (edgeFinset_mono hQG)
    dsimp [E]
    linarith
  rw [hweight]
  exact hb
end LightEFTSpanners
