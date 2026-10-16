import LightEFTSpanners.SubtreeHostFamily

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners HostCounting
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
variable {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
attribute [local instance] Classical.propDecidable

/-- Restrict actual non-seed edges to a host's vertex domain, and retain exactly
those whose original blocker set avoids its actual mapped tree. -/
noncomputable def subtreeAssignments (G Q : SimpleGraph V)
    (B : Sym2 V → Finset (Sym2 V)) (j : ∀ i, A i ↪ V)
    (T : ∀ i, SimpleGraph (A i)) (i : I) : Finset (Sym2 (A i)) :=
  (pullEdges (j i) (G.edgeFinset \ Q.edgeFinset)).filter
    (fun d => Disjoint (B ((j i).sym2Map d)) ((T i).map (j i)).edgeFinset)

/-- A supplied subtree packing with enough joint endpoint coverage gives the
coarse bound. The candidate assignment and its fault-avoidance votes are proved
from actual finite sets; the structural packing itself remains a premise. -/
theorem subtree_packing_lightness {G Q : SimpleGraph V} {w : Sym2 V → ℝ}
    {eps : ℝ} {f k h : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hQG : Q ≤ G) (hQpos : 0 < totalWeight Q w)
    (hB : BlockingData G Q.edgeFinset w ((1+eps)*(2*k-1)) f B)
    (indices : Finset I) (j : ∀ i, A i ↪ V) (T : ∀ i, SimpleGraph (A i))
    (htrees : ∀ i∈indices, (T i).IsTree)
    (htreeQ : ∀ i∈indices, (T i).map (j i) ≤ Q)
    (hcount : ∀ e∈G.edgeFinset \ Q.edgeFinset,
      2*f+h ≤ (indices.filter (fun i => ∃ d, (j i).sym2Map d=e)).card)
    (hcong : ∀ e∈Q.edgeFinset,
      (hosts indices (fun i => ((T i).map (j i)).edgeFinset) e).card ≤ 2)
    (hw : ∀ e∈G.edgeSet, 0 < w e) (hf : 0<f) (hk : 0<k) (heps : 0<eps)
    (hh : 0<h) :
    totalWeight G w / totalWeight Q w ≤
      1+8*(f:ℝ)*(8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹))/h := by
  classical
  have hcongAll (e : Sym2 V) :
      (hosts indices (fun i => ((T i).map (j i)).edgeFinset) e).card ≤ 2 := by
    by_cases he : e∈Q.edgeFinset
    · exact hcong e he
    · have heq : hosts indices (fun i => ((T i).map (j i)).edgeFinset) e=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨hi,heT⟩ := mem_filter.mp hi
        exact he (edgeFinset_mono (htreeQ i hi) heT)
      rw [heq]
      exact Nat.zero_le 2
  apply subtree_host_family_bound hQG hQpos hB indices j T
    (subtreeAssignments G Q B j T) htrees htreeQ
  · intro i _ e he
    have hs := (mem_pullEdges (j i) _ e).mp (mem_filter.mp he).1
    exact mem_edgeFinset.mp (mem_sdiff.mp hs).1
  · intro i _ e he
    exact (mem_sdiff.mp ((mem_pullEdges (j i) _ e).mp (mem_filter.mp he).1)).2
  · intro i _ e he
    exact (mem_filter.mp he).2
  · intro e he
    let goodDomain := indices.filter (fun i => ∃ d, (j i).sym2Map d=e)
    have hrestricted (d : Sym2 V) :
        (hosts goodDomain (fun i => ((T i).map (j i)).edgeFinset) d).card ≤ 2 := by
      apply (card_le_card (show hosts goodDomain (fun i => ((T i).map (j i)).edgeFinset) d ⊆
          hosts indices (fun i => ((T i).map (j i)).edgeFinset) d from ?_)).trans (hcongAll d)
      intro i hi
      obtain ⟨hi,hd⟩ := mem_filter.mp hi
      exact mem_filter.mpr ⟨(mem_filter.mp hi).1,hd⟩
    have hb := two_congestion_hosts goodDomain (fun i => ((T i).map (j i)).edgeFinset)
      (B e) f h (hcount e he) (hB.capped e) (fun d _ => hrestricted d)
    have heq : hosts indices (fun i => (subtreeAssignments G Q B j T i).map (j i).sym2Map) e =
        goodDomain.filter (fun i => Disjoint ((T i).map (j i)).edgeFinset (B e)) := by
      ext i
      constructor
      · intro hi
        obtain ⟨hi,hm⟩ := mem_filter.mp hi
        obtain ⟨d,hd,hde⟩ := mem_map.mp hm
        have ha := (mem_filter.mp hd).2
        rw [hde] at ha
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨hi,⟨d,hde⟩⟩,ha.symm⟩
      · intro hi
        obtain ⟨hi,ha⟩ := mem_filter.mp hi
        obtain ⟨hi,d,hde⟩ := mem_filter.mp hi
        apply mem_filter.mpr ⟨hi,?_⟩
        apply mem_map.mpr ⟨d,?_,hde⟩
        apply mem_filter.mpr
        constructor
        · apply (mem_pullEdges (j i) _ d).mpr
          rwa [hde]
        · rw [hde]
          exact ha.symm
    rwa [heq]
  · exact hcong
  · exact hw
  · exact hf
  · exact hk
  · exact heps
  · exact hh
end LightEFTSpanners
