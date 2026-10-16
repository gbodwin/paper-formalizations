import LightEFTSpanners.VotingSubtreeWeight
import LightEFTSpanners.VotingOutput

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

omit [DecidableEq I] in
theorem seed_union_list_weight (Q : SimpleGraph V) (w : Sym2 V → ℝ) (l : List (Sym2 V))
    (hn : l.Nodup) (hdis : ∀ e∈l,e∉Q.edgeFinset) (hdiag : ∀ e∈l,¬e.IsDiag) :
    totalWeight (edgeGraph (Q.edgeFinset∪l.toFinset)) w=totalWeight Q w+(l.map w).sum := by
  have hE : (edgeGraph (Q.edgeFinset∪l.toFinset)).edgeFinset=Q.edgeFinset∪l.toFinset := by
    ext e
    simp only [mem_edgeFinset,mem_edgeGraph]
    constructor
    · exact And.left
    · intro he
      refine ⟨he,?_⟩
      rcases mem_union.mp he with he | he
      · exact Q.not_isDiag_of_mem_edgeFinset he
      · exact hdiag e (List.mem_toFinset.mp he)
  have hd : Disjoint Q.edgeFinset l.toFinset := disjoint_left.mpr
    (fun e he hl => hdis e (List.mem_toFinset.mp hl) he)
  rw [weight_eq_edge_sum _ w _,hE,sum_union hd,List.sum_toFinset w hn,weight_eq_edge_sum Q w _]

/-- The actual empirical recursion has its seed baseline plus the weight of
its accepted records, and its good-event lightness follows from actual hosts. -/
theorem voting_output_weight_bound (G Q : SimpleGraph V) (hQ : Q≤G)
    (w : Sym2 V → ℝ) (eps : ℝ) (k f h : ℕ) (hk : 0<k) (heps : 0<eps) (hf : 0<f) (hh : 0<h)
    (indices : Finset I) (j : ∀ i,A i ↪ V) (T : ∀ i,SimpleGraph (A i))
    (eligible : Sym2 V → Finset I) (tape : Tape V I)
    (htree : ∀ i∈indices,(T i).IsTree) (htreeQ : ∀ i∈indices,(T i).map (j i)≤Q)
    (hsub : ∀ e∈G.edgeFinset\Q.edgeFinset,eligible e⊆indices)
    (himage : ∀ e∈G.edgeFinset\Q.edgeFinset,∀ i∈eligible e,∃ d,(j i).sym2Map d=e)
    (hcong : ∀ e∈Q.edgeFinset,
      (hosts indices (fun i => ((T i).map (j i)).edgeFinset) e).card≤2)
    (hw : ∀ e∈G.edgeSet,0<w e)
    (hacc : AccurateTrace Q.edgeFinset w ((1+eps)*(2*k-1)) f eligible
      (fun i => ((T i).map (j i)).edgeFinset) tape h (input G Q w)) :
    totalWeight (output G Q w ((1+eps)*(2*k-1)) eligible
      (fun i => ((T i).map (j i)).edgeFinset) tape h) w≤
      (1+64*(f:ℝ)*extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)/h)*totalWeight Q w := by
  let rs := history Q.edgeFinset w ((1+eps)*(2*k-1)) eligible
    (fun i => ((T i).map (j i)).edgeFinset) tape h (input G Q w)
  have hsl := history_sublist Q.edgeFinset w ((1+eps)*(2*k-1)) eligible
    (fun i => ((T i).map (j i)).edgeFinset) tape h (input G Q w)
  have hin (e) (he : e∈rs.map Prod.fst) : e∈G.edgeFinset\Q.edgeFinset :=
    mem_sdiff.mpr ((mem_input G Q w e).mp (hsl.subset he))
  have hnd := hsl.nodup (input_nodup G Q w)
  have hdi (e) (he : e∈rs.map Prod.fst) : ¬e.IsDiag :=
    G.not_isDiag_of_mem_edgeFinset (mem_sdiff.mp (hin e he)).1
  have hdis (e) (he : e∈rs.map Prod.fst) : e∉Q.edgeFinset := (mem_sdiff.mp (hin e he)).2
  have hg := history_approved Q.edgeFinset w ((1+eps)*(2*k-1)) f h eligible
    (fun i => ((T i).map (j i)).edgeFinset) tape (input G Q w) hacc
  have hb := voting_subtree_weight Q w eps k f h hk heps hf indices j T eligible rs htree htreeQ
    (fun e he => hsub e (hin e he)) (fun e he => himage e (hin e he)) hcong
    ((input_sorted G Q w).sublist hsl) hnd hdis hdi
    (by
      intro e he
      rcases mem_union.mp he with he | he
      · exact hw e (edgeSet_mono hQ (mem_edgeFinset.mp he))
      · exact hw e (mem_edgeFinset.mp (mem_sdiff.mp (hin e (List.mem_toFinset.mp he))).1)) hg
  have hweight : totalWeight (output G Q w ((1+eps)*(2*k-1)) eligible
      (fun i => ((T i).map (j i)).edgeFinset) tape h) w=
      totalWeight Q w+(rs.map (fun r => w r.1)).sum := by
    rw [output,history_edges,seed_union_list_weight _ _ _ hnd hdis hdi]
    simp only [List.map_map,Function.comp_def,rs]
  rw [hweight]
  have hr : (0:ℝ)<h := by exact_mod_cast hh
  have hb' : (rs.map (fun r => w r.1)).sum≤
      (64*(f:ℝ)*extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)*totalWeight Q w)/(h:ℝ) :=
    (le_div_iff₀ hr).mpr (by nlinarith [hb])
  calc
    _ ≤ totalWeight Q w+(64*(f:ℝ)*extremalLightness (Fintype.card V)
      ((1+eps)*(2*k-1)+1)*totalWeight Q w)/(h:ℝ) := add_le_add (le_refl _) hb'
    _ = _ := by ring
end LightEFTSpanners.SampledGreedy
