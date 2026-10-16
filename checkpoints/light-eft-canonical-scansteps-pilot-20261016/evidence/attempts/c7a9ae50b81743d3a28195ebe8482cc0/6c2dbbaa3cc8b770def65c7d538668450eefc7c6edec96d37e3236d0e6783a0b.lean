import LightEFTSpanners.AssignedHostExtremal
import LightEFTSpanners.VotingWeightIncidence
import LightEFTSpanners.HostCounting

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners HostCounting
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
attribute [local instance] Classical.propDecidable

omit [DecidableEq V] in
private theorem weight_eq_edge_sum (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (a : Fintype G.edgeSet) : totalWeight G w=∑ e∈@SimpleGraph.edgeFinset V G a,w e := by
  unfold totalWeight
  have hh (a b : Fintype G.edgeSet) :
      (∑ e∈@SimpleGraph.edgeFinset V G a,w e)=∑ e∈@SimpleGraph.edgeFinset V G b,w e := by
    cases Subsingleton.elim a b;rfl
  exact hh _ _

/-- The actual accepted voting history is charged to genuine embedded tree
hosts. Every original host edge is charged at most twice. -/
theorem voting_subtree_weight (Q : SimpleGraph V) (w : Sym2 V → ℝ) (eps : ℝ) (k f h : ℕ)
    (hk : 0<k) (heps : 0<eps) (hf : 0<f)
    (indices : Finset I) (j : ∀ i,A i ↪ V) (T : ∀ i,SimpleGraph (A i))
    (eligible : Sym2 V → Finset I) (rs : List (Sym2 V × Finset I))
    (htree : ∀ i∈indices,(T i).IsTree) (htreeQ : ∀ i∈indices,(T i).map (j i)≤Q)
    (hsub : ∀ e∈rs.map Prod.fst,eligible e⊆indices)
    (himage : ∀ e∈rs.map Prod.fst,∀ i∈eligible e,∃ d,(j i).sym2Map d=e)
    (hcong : ∀ e∈Q.edgeFinset,
      (hosts indices (fun i => ((T i).map (j i)).edgeFinset) e).card≤2)
    (hs : (rs.map Prod.fst).Pairwise (fun e d => w d≤w e))
    (hn : (rs.map Prod.fst).Nodup) (hdis : ∀ e∈rs.map Prod.fst,e∉Q.edgeFinset)
    (hdiag : ∀ e∈rs.map Prod.fst,¬e.IsDiag)
    (hw : ∀ e∈Q.edgeFinset∪(rs.map Prod.fst).toFinset,0<w e)
    (hg : ApprovedHistory Q.edgeFinset w ((1+eps)*(2*k-1)) f h eligible
      (fun i => ((T i).map (j i)).edgeFinset) rs) :
    (h:ℝ)*(rs.map (fun r => w r.1)).sum≤64*(f:ℝ)*
      extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)*totalWeight Q w := by
  let L := extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)
  have hL : 0≤L := extremalLightness_nonneg _ (actual_threshold_gt_two heps hk)
  have hmult := voting_weight_incidence Q.edgeFinset w ((1+eps)*(2*k-1)) f h eligible
    (fun i => ((T i).map (j i)).edgeFinset) indices rs hsub
    (fun e he => (hw e (mem_union_right _ (List.mem_toFinset.mpr he))).le) hg
  have hper : (∑ i∈indices,assignedWeight w i rs)≤
      32*(f:ℝ)*L*(∑ i∈indices,totalWeight ((T i).map (j i)) w) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    apply assigned_host_extremal_bound (j i) (T i) (htree i hi) Q.edgeFinset w eps k f h
      hk heps hf eligible (fun i => ((T i).map (j i)).edgeFinset) i rfl
      (edgeFinset_mono (htreeQ i hi)) rs hs hn hdis hdiag ?_ hw hg
    intro e B he hiB
    exact himage e (List.mem_map.mpr ⟨(e,B),he,rfl⟩) i ((approved_record hg he).1 hiB)
  have htreeSub : ∀ i∈indices,((T i).map (j i)).edgeFinset⊆Q.edgeFinset :=
    fun i hi => edgeFinset_mono (htreeQ i hi)
  have htinc := weighted_incidence indices Q.edgeFinset
    (fun i => ((T i).map (j i)).edgeFinset) w htreeSub
  have htw : (∑ i∈indices,totalWeight ((T i).map (j i)) w)≤2*totalWeight Q w := by
    have heq : (∑ i∈indices,totalWeight ((T i).map (j i)) w)=
        ∑ i∈indices,∑ e∈((T i).map (j i)).edgeFinset,w e := by
      apply sum_congr rfl;intro i _;exact weight_eq_edge_sum _ w _
    rw [heq,weight_eq_edge_sum Q w _,htinc,mul_sum]
    apply sum_le_sum
    intro e he
    have hc : ((hosts indices (fun i => ((T i).map (j i)).edgeFinset) e).card:ℝ)≤2 := by
      exact_mod_cast hcong e he
    exact mul_le_mul_of_nonneg_right hc (hw e (mem_union_left _ he)).le
  have hz := mul_le_mul_of_nonneg_left htw (show (0:ℝ)≤32*(f:ℝ)*L by positivity)
  exact (hmult.trans hper).trans (by nlinarith)
end LightEFTSpanners.SampledGreedy
