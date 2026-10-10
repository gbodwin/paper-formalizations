import MinorFreeSpanners.StarNeighborhoodUnion

/-! Actual mate incidences bound the number of other stars mated to one
fixed star. This establishes the mated part of the cleaning count; the
unmated bad-pair argument remains separate. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- All genuine common-neighbor mates of some vertex in S. -/
noncomputable def starMateUnion (G : SimpleGraph V) (q : ℝ) (S : Finset V) : Finset V :=
  S.biUnion fun x => Finset.univ.filter fun y =>
    q ≤ (Fintype.card (G.commonNeighbors x y):ℝ)

/-- Other selected stars with a literal cross-branch mate witness. -/
noncomputable def matedStarCenters (G : SimpleGraph V) (q : ℝ)
    (C : Finset V) (L : V → Finset V) (b : V) : Finset V :=
  C.filter fun c => c≠b ∧ ∃ x ∈ insert b (L b), ∃ y ∈ insert c (L c),
    q ≤ (Fintype.card (G.commonNeighbors x y):ℝ)

/-- Distinct actual branch owners inject into the actual mate union. -/
theorem IsStarPacking.matedStarCenters_card_le {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) (q : ℝ) (b : V) :
    (matedStarCenters G q C L b).card ≤
      (starMateUnion G q (insert b (L b))).card := by
  have hs : matedStarCenters G q C L b ⊆
      starHitCenters C L (starMateUnion G q (insert b (L b))) := by
    intro c hc
    obtain ⟨hc,_,x,hx,y,hy,hq⟩ := Finset.mem_filter.mp hc
    apply Finset.mem_filter.mpr
    refine ⟨hc,y,?_,hy⟩
    exact Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq⟩⟩
  exact (Finset.card_le_card hs).trans (h.starHitCenters_card hAC _)

/-- Literal Unmated and actual small branch vertices give the source's
(ell+1)*epsilon1*d bound on mated neighboring stars. No bad-pair oracle or
loss bound is assumed. -/
theorem IsStarPacking.matedStarCenters_bound {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) (K eps1 eps2 d : ℝ)
    (hG : Unmated G K eps1 eps2 d) {b : V} (hb : b ∈ C)
    (hfull : (L b).card=ell)
    (hsmall : ∀ x ∈ insert b (L b), (G.degree x:ℝ) ≤ K*d) :
    ((matedStarCenters G (eps2*d) C L b).card:ℝ) ≤
      (ell+1)*eps1*d := by
  classical
  have hc := h.matedStarCenters_card_le hAC (eps2*d) b
  have hu : (starMateUnion G (eps2*d) (insert b (L b))).card ≤
      ∑ x ∈ insert b (L b), (Finset.univ.filter fun y =>
        eps2*d ≤ (Fintype.card (G.commonNeighbors x y):ℝ)).card := Finset.card_biUnion_le
  have hr := Nat.cast_le (α:=ℝ).mpr (hc.trans hu)
  have hm : ((∑ x ∈ insert b (L b), (Finset.univ.filter fun y =>
        eps2*d ≤ (Fintype.card (G.commonNeighbors x y):ℝ)).card : ℕ):ℝ) ≤
      ((insert b (L b)).card:ℝ)*(eps1*d) := by
    push_cast
    calc
      _ ≤ ∑ _x ∈ insert b (L b), (eps1*d) := by
        apply Finset.sum_le_sum
        intro x hx
        exact (hG x (hsmall x hx)).le
      _ = _ := by simp
  have hnot : b ∉ L b := fun hx => Finset.disjoint_left.mp hAC (h.2.1 b hx) hb
  have hcard : (insert b (L b)).card=ell+1 := by rw [Finset.card_insert_of_notMem hnot,hfull]
  rw [hcard,Nat.cast_add,Nat.cast_one] at hm
  exact (hr.trans hm).trans_eq (by ring)

/-- Absence from the actual mated-center set, together with the two original
mate-free branches, supplies exactly the original-host union premise
required by the concrete two-star exchange. -/
theorem not_matedStarCenters_union_mateFree (G : SimpleGraph V) (q : ℝ)
    (C : Finset V) (L : V → Finset V) {b c : V} (hc : c ∈ C) (hcb : c ≠ b)
    (hn : c ∉ matedStarCenters G q C L b)
    (hbfree : MateFreeOn G q (↑(insert b (L b)) : Set V))
    (hcfree : MateFreeOn G q (↑(insert c (L c)) : Set V)) :
    MateFreeOn G q (↑(insert b (L b) ∪ insert c (L c)) : Set V) := by
  classical
  have hcross : ∀ x ∈ insert b (L b), ∀ y ∈ insert c (L c),
      (Fintype.card (G.commonNeighbors x y):ℝ) < q := by
    intro x hx y hy
    by_contra hlt
    exact hn (Finset.mem_filter.mpr ⟨hc,hcb,x,hx,y,hy,le_of_not_gt hlt⟩)
  intro x hx y hy hxy
  simp only [Finset.coe_union,Set.mem_union] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hbfree x hx y hy hxy
  · exact hcross x hx y hy
  · simpa only [G.commonNeighbors_symm y x] using hcross y hy x hx
  · exact hcfree x hx y hy hxy

end MinorFreeSpanners
