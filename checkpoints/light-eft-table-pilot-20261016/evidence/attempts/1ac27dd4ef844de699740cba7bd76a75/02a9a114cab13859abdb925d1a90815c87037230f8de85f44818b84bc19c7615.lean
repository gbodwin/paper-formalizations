import LightEFTSpanners.InducedHostLocalCap
import LightEFTSpanners.HostCounting

/-! Actual weight aggregation for a supplied family of trees on different
embedded vertex types. Packing existence and candidate coverage remain explicit. -/
namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners HostCounting
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
variable {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
attribute [local instance] Classical.propDecidable

omit [DecidableEq V] in
private theorem weight_eq_edge_sum (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (a : Fintype G.edgeSet) :
    totalWeight G w = ∑ e∈@SimpleGraph.edgeFinset V G a,w e := by
  unfold totalWeight
  have hh (a b : Fintype G.edgeSet) :
      (∑ e∈@SimpleGraph.edgeFinset V G a,w e) =
        ∑ e∈@SimpleGraph.edgeFinset V G b,w e := by
    cases Subsingleton.elim a b
    rfl
  exact hh _ _

/-- Actual weight charging for any subset of non-seed candidates, using its
local residual blocker cap and genuine coverage multiplicity. -/
theorem subtree_candidate_weight_bound {G Q : SimpleGraph V} {w : Sym2 V → ℝ}
    {eps : ℝ} {f k h r : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hQG : Q≤G)
    (hB : BlockingData G Q.edgeFinset w ((1+eps)*(2*k-1)) f B)
    (E : Finset (Sym2 V)) (hE : E⊆G.edgeFinset \ Q.edgeFinset)
    (indices : Finset I) (j : ∀ i, A i ↪ V)
    (T : ∀ i, SimpleGraph (A i)) (U : ∀ i, Finset (Sym2 (A i)))
    (htrees : ∀ i∈indices,(T i).IsTree) (htreeQ : ∀ i∈indices,(T i).map (j i)≤Q)
    (hUG : ∀ i∈indices,∀ e∈U i,(j i).sym2Map e∈G.edgeSet)
    (hUQ : ∀ i∈indices,∀ e∈U i,(j i).sym2Map e∉Q.edgeFinset)
    (hhost : ∀ i∈indices,∀ e∈U i,Disjoint (B ((j i).sym2Map e)) ((T i).map (j i)).edgeFinset)
    (hUE : ∀ i∈indices, (U i).map (j i).sym2Map⊆E)
    (hcap : ∀ i∈indices,∀ e∈U i,(B ((j i).sym2Map e) \ Q.edgeFinset).card≤r)
    (hcover : ∀ e∈E,h≤(hosts indices (fun i => (U i).map (j i).sym2Map) e).card)
    (hcong : ∀ e∈Q.edgeFinset,(hosts indices (fun i => ((T i).map (j i)).edgeFinset) e).card≤2)
    (hw : ∀ e∈G.edgeSet,0<w e) (hr : 0<r) (hk : 0<k) (heps : 0<eps)
    : (h:ℝ)*(∑ e∈E,w e) ≤
      8*(r:ℝ)*(8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹))*totalWeight Q w := by
  classical
  let L : ℝ := 8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹)
  have hL : 0≤L := by dsimp [L]; positivity
  have hinc := weighted_incidence indices E (fun i => (U i).map (j i).sym2Map) w hUE
  have hmult : (h:ℝ)*(∑ e∈E,w e) ≤ ∑ i∈indices,∑ e∈(U i).map (j i).sym2Map,w e := by
    rw [hinc,mul_sum]
    apply sum_le_sum
    intro e he
    have hh' : (h:ℝ)≤(hosts indices (fun i => (U i).map (j i).sym2Map) e).card := by exact_mod_cast hcover e he
    exact mul_le_mul_of_nonneg_right hh' (hw e (mem_edgeFinset.mp (mem_sdiff.mp (hE he)).1)).le
  have hper : (∑ i∈indices,∑ e∈(U i).map (j i).sym2Map,w e) ≤
      4*(r:ℝ)*L*(∑ i∈indices,totalWeight ((T i).map (j i)) w) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    exact induced_host_local_cap_global_order (j i) hQG hB (htrees i hi)
      (htreeQ i hi) (U i) (hUG i hi) (hUQ i hi) (hhost i hi) (hcap i hi) hw hr hk heps
  have htreeSub : ∀ i∈indices,((T i).map (j i)).edgeFinset⊆Q.edgeFinset := by
    intro i hi
    exact edgeFinset_mono (htreeQ i hi)
  have htinc := weighted_incidence indices Q.edgeFinset (fun i => ((T i).map (j i)).edgeFinset) w htreeSub
  have htw : (∑ i∈indices,totalWeight ((T i).map (j i)) w)≤2*totalWeight Q w := by
    have heq : (∑ i∈indices,totalWeight ((T i).map (j i)) w) =
        ∑ i∈indices,∑ e∈((T i).map (j i)).edgeFinset,w e := by
      apply sum_congr rfl
      intro i _
      exact weight_eq_edge_sum _ w _
    rw [heq,weight_eq_edge_sum Q w _,htinc,mul_sum]
    apply sum_le_sum
    intro e he
    have hc : ((hosts indices (fun i => ((T i).map (j i)).edgeFinset) e).card:ℝ)≤2 := by
      exact_mod_cast hcong e he
    exact mul_le_mul_of_nonneg_right hc (hw e (edgeSet_mono hQG (mem_edgeFinset.mp he))).le
  have hscale : 0≤4*(r:ℝ)*L := by positivity
  have hs := mul_le_mul_of_nonneg_left htw hscale
  calc
    (h:ℝ)*(∑ e∈E,w e) ≤ _ := hmult.trans hper
    _ ≤ 4*(r:ℝ)*L*(2*totalWeight Q w) := hs
    _ = 8*(r:ℝ)*L*totalWeight Q w := by ring
end LightEFTSpanners
