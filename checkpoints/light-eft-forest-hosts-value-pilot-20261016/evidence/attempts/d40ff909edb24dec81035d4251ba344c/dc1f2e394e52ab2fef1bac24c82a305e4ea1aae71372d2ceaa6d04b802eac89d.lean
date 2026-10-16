import LightEFTSpanners.SubtreeCandidateWeight

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners HostCounting
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
variable {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
attribute [local instance] Classical.propDecidable

noncomputable def candidateAssignments (E : Finset (Sym2 V))
    (B : Sym2 V → Finset (Sym2 V)) (j : ∀ i, A i ↪ V)
    (T : ∀ i, SimpleGraph (A i)) (i : I) : Finset (Sym2 (A i)) :=
  (pullEdges (j i) E).filter
    (fun d => Disjoint (B ((j i).sym2Map d)) ((T i).map (j i)).edgeFinset)

/-- Only seed blockers can spoil a host tree. The local sample cap is a
separate quantity, bounding the residual non-seed blockers of candidates. -/
theorem candidate_packing_weight_bound {G Q : SimpleGraph V} {w : Sym2 V → ℝ}
    {eps : ℝ} {f k h r b : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hQG : Q≤G) (hB : BlockingData G Q.edgeFinset w ((1+eps)*(2*k-1)) f B)
    (E : Finset (Sym2 V)) (hE : E⊆G.edgeFinset \ Q.edgeFinset)
    (indices : Finset I) (j : ∀ i, A i ↪ V) (T : ∀ i, SimpleGraph (A i))
    (htrees : ∀ i∈indices,(T i).IsTree) (htreeQ : ∀ i∈indices,(T i).map (j i)≤Q)
    (hcount : ∀ e∈E,2*b+h≤(indices.filter (fun i => ∃ d,(j i).sym2Map d=e)).card)
    (hseedcap : ∀ e∈E,(B e∩Q.edgeFinset).card≤b)
    (hcap : ∀ e∈E,(B e\Q.edgeFinset).card≤r)
    (hcong : ∀ e∈Q.edgeFinset,(hosts indices (fun i => ((T i).map (j i)).edgeFinset) e).card≤2)
    (hw : ∀ e∈G.edgeSet,0<w e) (hr : 0<r) (hk : 0<k) (heps : 0<eps) :
    (h:ℝ)*(∑ e∈E,w e) ≤
      8*(r:ℝ)*(8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹))*totalWeight Q w := by
  classical
  let U := candidateAssignments E B j T
  have hUE : ∀ i∈indices,(U i).map (j i).sym2Map⊆E := by
    intro i _ e he
    obtain ⟨d,hd,rfl⟩ := mem_map.mp he
    exact (mem_pullEdges (j i) E d).mp (mem_filter.mp hd).1
  apply subtree_candidate_weight_bound hQG hB E hE indices j T U htrees htreeQ
  · intro i hi e he
    exact mem_edgeFinset.mp (mem_sdiff.mp (hE (hUE i hi (mem_map.mpr ⟨e,he,rfl⟩)))).1
  · intro i hi e he
    exact (mem_sdiff.mp (hE (hUE i hi (mem_map.mpr ⟨e,he,rfl⟩)))).2
  · intro i _ e he
    exact (mem_filter.mp he).2
  · exact hUE
  · intro i hi e he
    exact hcap _ (hUE i hi (mem_map.mpr ⟨e,he,rfl⟩))
  · intro e he
    let D := indices.filter (fun i => ∃ d,(j i).sym2Map d=e)
    have hrestricted (d : Sym2 V) (hd : d∈B e∩Q.edgeFinset) :
        (hosts D (fun i => ((T i).map (j i)).edgeFinset) d).card≤2 := by
      apply (card_le_card (show hosts D (fun i => ((T i).map (j i)).edgeFinset) d ⊆
          hosts indices (fun i => ((T i).map (j i)).edgeFinset) d from ?_)).trans (hcong d (mem_inter.mp hd).2)
      intro i hi
      obtain ⟨hi,hd⟩ := mem_filter.mp hi
      exact mem_filter.mpr ⟨(mem_filter.mp hi).1,hd⟩
    have hc := two_congestion_hosts D (fun i => ((T i).map (j i)).edgeFinset)
      (B e∩Q.edgeFinset) b h (hcount e he) (hseedcap e he) hrestricted
    have hdj (i : I) (hi : i∈indices) :
        Disjoint ((T i).map (j i)).edgeFinset (B e∩Q.edgeFinset) ↔
        Disjoint ((T i).map (j i)).edgeFinset (B e) := by
      constructor
      · intro hh
        apply Finset.disjoint_left.mpr
        intro d hd hb
        exact Finset.disjoint_left.mp hh hd (mem_inter.mpr ⟨hb,edgeFinset_mono (htreeQ i hi) hd⟩)
      · intro hh
        exact hh.mono_right inter_subset_left
    have heq : hosts indices (fun i => (U i).map (j i).sym2Map) e =
        D.filter (fun i => Disjoint ((T i).map (j i)).edgeFinset (B e∩Q.edgeFinset)) := by
      ext i
      constructor
      · intro hi
        obtain ⟨hi,hm⟩ := mem_filter.mp hi
        obtain ⟨d,hd,hde⟩ := mem_map.mp hm
        have ha := (mem_filter.mp hd).2
        rw [hde] at ha
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨hi,⟨d,hde⟩⟩,(hdj i hi).mpr ha.symm⟩
      · intro hi
        obtain ⟨hi,ha⟩ := mem_filter.mp hi
        obtain ⟨hi,d,hde⟩ := mem_filter.mp hi
        apply mem_filter.mpr ⟨hi,?_⟩
        apply mem_map.mpr ⟨d,?_,hde⟩
        apply mem_filter.mpr
        constructor
        · apply (mem_pullEdges (j i) E d).mpr
          rwa [hde]
        · rw [hde]
          exact ((hdj i hi).mp ha).symm
    rwa [heq]
  · exact hcong
  · exact hw
  · exact hr
  · exact hk
  · exact heps
end LightEFTSpanners
