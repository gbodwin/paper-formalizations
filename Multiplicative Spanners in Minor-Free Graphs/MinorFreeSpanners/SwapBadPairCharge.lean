import MinorFreeSpanners.TwoStarLeafSwap
import MinorFreeSpanners.StarCrossingFiber
import MinorFreeSpanners.CommonNeighborIncidences

/-! Exact local effects of the literal two-leaf exchange on directed crossing
sets. A newly bad pair need not use the inserted leaf: the alternative is
charged to an actual original-host common neighbor of two old leaves.
No minimum-score, global cleaning, or density claim is made. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*}
variable {G : SimpleGraph V} {A B C : Finset V} {ell : ℕ}
  {L : V → Finset V} {b c u v d : V}

/-- Exact forward crossing update at the first exchanged star. -/
theorem IsStarPacking.twoStarLeafSwap_cross_left (h : IsStarPacking G A C ell L)
    (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c) (d : V) :
    starCrossLeaves G (MinorFreeSpanners.twoStarLeafSwap L u v) b d =
      if G.Adj v d then insert v ((starCrossLeaves G L b d).erase u)
      else (starCrossLeaves G L b d).erase u := by
  simp only [starCrossLeaves,h.twoStarLeafSwap_at_left hbc hu hv,
    Finset.filter_insert,Finset.filter_erase]

/-- The symmetric exact forward crossing update. -/
theorem IsStarPacking.twoStarLeafSwap_cross_right (h : IsStarPacking G A C ell L)
    (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c) (d : V) :
    starCrossLeaves G (MinorFreeSpanners.twoStarLeafSwap L u v) c d =
      if G.Adj u d then insert u ((starCrossLeaves G L c d).erase v)
      else (starCrossLeaves G L c d).erase v := by
  simp only [starCrossLeaves,h.twoStarLeafSwap_at_right hbc hu hv,
    Finset.filter_insert,Finset.filter_erase]

/-- An unchanged third star has the same crossings to every fixed center. -/
theorem IsStarPacking.twoStarLeafSwap_cross_other (h : IsStarPacking G A C ell L)
    (hu : u ∈ L b) (hv : v ∈ L c) (hdb : d ≠ b) (hdc : d ≠ c) (e : V) :
    starCrossLeaves G (MinorFreeSpanners.twoStarLeafSwap L u v) d e = starCrossLeaves G L d e := by
  simp only [starCrossLeaves,h.twoStarLeafSwap_at_other hu hv hdb hdc]

/-- Without inserted-leaf adjacency, a new bad pair is caused by removing one
of exactly two old forward crossings. Both old leaves meet the actual third
center in G; this is not a premise about abstract incidence counts. -/
theorem IsStarPacking.twoStarLeafSwap_new_bad_common_neighbor
    (h : IsStarPacking G A C ell L) (hbc : b ≠ c)
    (hu : u ∈ L b) (hv : v ∈ L c) (hdb : d ≠ b) (hdc : d ≠ c)
    (hnew : IsBadStarPair G (MinorFreeSpanners.twoStarLeafSwap L u v) b d)
    (hold : ¬ IsBadStarPair G L b d) (hvd : ¬ G.Adj v d) :
    (starCrossLeaves G L b d).card = 2 ∧
      ∃ w ∈ (L b).erase u, G.Adj u d ∧ G.Adj w d := by
  have hf : (starCrossLeaves G L b d).erase u =
      starCrossLeaves G (MinorFreeSpanners.twoStarLeafSwap L u v) b d := by
    rw [h.twoStarLeafSwap_cross_left hbc hu hv d,ite_eq_right hvd]
  have hr : (starCrossLeaves G L d b).card = 1 := by
    rw [← h.twoStarLeafSwap_cross_other hu hv hdb hdc b]
    exact hnew.2.2
  have hud : G.Adj u d := by
    by_contra hn
    have hnot : u ∉ starCrossLeaves G L b d := by simp [starCrossLeaves,hn]
    have he := hf
    rw [Finset.erase_eq_of_notMem hnot] at he
    exact hold ⟨hnew.1,by rw [he]; exact hnew.2.1,hr⟩
  have hum : u ∈ starCrossLeaves G L b d := Finset.mem_filter.mpr ⟨hu,hud⟩
  have hc := Finset.card_erase_add_one hum
  rw [hf,hnew.2.1] at hc
  refine ⟨by omega,?_⟩
  have hp : 0 < ((starCrossLeaves G L b d).erase u).card := by
    rw [hf,hnew.2.1]; omega
  obtain ⟨w,hw⟩ := Finset.card_pos.mp hp
  obtain ⟨hwu,hw⟩ := Finset.mem_erase.mp hw
  obtain ⟨hw,hadj⟩ := Finset.mem_filter.mp hw
  exact ⟨w,Finset.mem_erase.mpr ⟨hwu,hw⟩,hud,hadj⟩

/-- The same concrete classification at the second exchanged star. -/
theorem IsStarPacking.twoStarLeafSwap_new_bad_common_neighbor_right
    (h : IsStarPacking G A C ell L) (hbc : b ≠ c)
    (hu : u ∈ L b) (hv : v ∈ L c) (hdb : d ≠ b) (hdc : d ≠ c)
    (hnew : IsBadStarPair G (MinorFreeSpanners.twoStarLeafSwap L u v) c d)
    (hold : ¬ IsBadStarPair G L c d) (hud : ¬ G.Adj u d) :
    (starCrossLeaves G L c d).card = 2 ∧
      ∃ w ∈ (L c).erase v, G.Adj v d ∧ G.Adj w d := by
  have hs : MinorFreeSpanners.twoStarLeafSwap L v u =
      MinorFreeSpanners.twoStarLeafSwap L u v := by
    funext e
    simp only [MinorFreeSpanners.twoStarLeafSwap,Equiv.swap_comm v u]
  exact h.twoStarLeafSwap_new_bad_common_neighbor hbc.symm hv hu hdc hdb
    (by rw [hs]; exact hnew) hold hud

/-- A finite collection of actual newly bad third centers whose inserted
leaf is not adjacent. All badness is measured in the fixed original host G. -/
noncomputable def swapNewBadNoInserted (G : SimpleGraph V) (L : V → Finset V)
    (b c u v : V) (D : Finset V) : Finset V :=
  D.filter fun d => d ≠ b ∧ d ≠ c ∧
    IsBadStarPair G (MinorFreeSpanners.twoStarLeafSwap L u v) b d ∧
    ¬ IsBadStarPair G L b d ∧ ¬ G.Adj v d

/-- Every exceptional center is in an explicit union of real common-neighbor
slices. The supplied finite center set is retained in the charging target. -/
theorem IsStarPacking.swapNewBadNoInserted_subset
    (h : IsStarPacking G A C ell L) (hbc : b ≠ c)
    (hu : u ∈ L b) (hv : v ∈ L c) (D : Finset V) :
    swapNewBadNoInserted G L b c u v D ⊆
      ((L b).erase u).biUnion (fun w => D.filter fun d => G.Adj u d ∧ G.Adj w d) := by
  intro d hd
  obtain ⟨hd,hdb,hdc,hnew,hold,hvd⟩ := Finset.mem_filter.mp hd
  obtain ⟨_,w,hw,hud,hwd⟩ :=
    h.twoStarLeafSwap_new_bad_common_neighbor hbc hu hv hdb hdc hnew hold hvd
  exact Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_filter.mpr ⟨hd,hud,hwd⟩⟩

/-- Finite union bound with the literal original-host incidences. -/
theorem IsStarPacking.swapNewBadNoInserted_card_le_slices
    (h : IsStarPacking G A C ell L) (hbc : b ≠ c)
    (hu : u ∈ L b) (hv : v ∈ L c) (D : Finset V) :
    (swapNewBadNoInserted G L b c u v D).card ≤
      ∑ w ∈ (L b).erase u, (D.filter fun d => G.Adj u d ∧ G.Adj w d).card := by
  exact (Finset.card_le_card (h.swapNewBadNoInserted_subset hbc hu hv D)).trans
    (Finset.card_biUnion_le)

variable [Fintype V]

/-- Bound exceptional centers by full actual common-neighbor cardinalities. -/
theorem IsStarPacking.swapNewBadNoInserted_card_le_commonNeighbors
    (h : IsStarPacking G A C ell L) (hbc : b ≠ c)
    (hu : u ∈ L b) (hv : v ∈ L c) (D : Finset V) :
    (swapNewBadNoInserted G L b c u v D).card ≤
      ∑ w ∈ (L b).erase u, Fintype.card (G.commonNeighbors u w) := by
  apply (h.swapNewBadNoInserted_card_le_slices hbc hu hv D).trans
  apply Finset.sum_le_sum
  intro w _
  calc
    (D.filter fun d => G.Adj u d ∧ G.Adj w d).card ≤
        (G.commonNeighbors u w).toFinset.card := by
      apply Finset.card_le_card
      intro d hd
      exact Set.mem_toFinset.mpr (Finset.mem_filter.mp hd).2
    _ = _ := Set.toFinset_card _

/-- Original-host mate-freeness of the old branch yields a quantitative bound.
This does not assert that the exchanged branches are themselves mate-free. -/
theorem IsStarPacking.swapNewBadNoInserted_card_le_mateFree
    (h : IsStarPacking G A C ell L) (hbc : b ≠ c)
    (hu : u ∈ L b) (hv : v ∈ L c) (D : Finset V) {q : ℝ}
    (hfree : MateFreeOn G q (↑(insert b (L b)) : Set V)) :
    ((swapNewBadNoInserted G L b c u v D).card : ℝ) ≤ ((L b).erase u).card * q := by
  have hn := h.swapNewBadNoInserted_card_le_commonNeighbors hbc hu hv D
  calc
    ((swapNewBadNoInserted G L b c u v D).card : ℝ) ≤
        ((∑ w ∈ (L b).erase u, Fintype.card (G.commonNeighbors u w) : ℕ) : ℝ) :=
      Nat.cast_le.mpr hn
    _ = ∑ w ∈ (L b).erase u, (Fintype.card (G.commonNeighbors u w) : ℝ) := by
      push_cast; rfl
    _ ≤ ∑ _w ∈ (L b).erase u, q := by
      apply Finset.sum_le_sum
      intro w hw
      obtain ⟨hwu,hw⟩ := Finset.mem_erase.mp hw
      exact (hfree u (Finset.mem_insert_of_mem hu) w (Finset.mem_insert_of_mem hw)
        hwu.symm).le
    _ = _ := by simp

/-- In the actual full simple quotient, a bad selected pair has one quotient
edge, two crossing host edges in its fiber, and suppression surplus one. -/
theorem IsStarPacking.badStarPair_selected_fiber_two
    (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V)) (hCB : C ⊆ B)
    (b d : C) (hbad : IsBadStarPair G L b.val d.val) :
    (fullStarContraction G C L).Adj (Sum.inl b) (Sum.inl d) ∧
    let F := (quotientCrossEdges G (fullStarLabel C L)).filter fun e =>
      Sym2.map (fullStarLabel C L) e = s(Sum.inl b,Sum.inl d)
    F.card = 2 ∧ F.card - 1 = 1 := by
  have hbd : b ≠ d := fun he => hbad.1 (congrArg Subtype.val he)
  have hf := h.selected_edge_fiber_card hG hCB b d hbd
  rw [hbad.2.1,hbad.2.2] at hf
  have hp : 0 < (starCrossLeaves G L b.val d.val).card := by rw [hbad.2.1]; omega
  obtain ⟨w,hw⟩ := Finset.card_pos.mp hp
  obtain ⟨hw,hwd⟩ := Finset.mem_filter.mp hw
  refine ⟨?_,hf,by omega⟩
  exact ⟨fun he => hbd (Sum.inl.inj he),w,
    Finset.mem_insert_of_mem hw,d.val,Finset.mem_insert_self _ _,hwd⟩

/-- The fiber conclusion for the literal exchanged family, whose validity is
proved from real cross edges in the bipartite host. No mate-freeness of the
new family is inferred here. -/
theorem IsStarPacking.twoStarLeafSwap_bad_selected_fiber_two
    (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V)) (hCB : C ⊆ B)
    (hu : u ∈ L b) (hv : v ∈ L c) (hbv : G.Adj b v) (hcu : G.Adj c u)
    (s t : C) (hbad : IsBadStarPair G (MinorFreeSpanners.twoStarLeafSwap L u v) s.val t.val) :
    (fullStarContraction G C (MinorFreeSpanners.twoStarLeafSwap L u v)).Adj (Sum.inl s) (Sum.inl t) ∧
    let F := (quotientCrossEdges G (fullStarLabel C (MinorFreeSpanners.twoStarLeafSwap L u v))).filter fun e =>
      Sym2.map (fullStarLabel C (MinorFreeSpanners.twoStarLeafSwap L u v)) e = s(Sum.inl s,Sum.inl t)
    F.card = 2 ∧ F.card - 1 = 1 := by
  exact (h.twoStarLeafSwap_valid hG hu hv hbv hcu).badStarPair_selected_fiber_two
    hG hCB s t hbad

/-- A bounded admissible exchange and the concrete exceptional-pair witness.
Admissibility keeps both the old branchwise and exchanged-union nonmate
premises in the original host. The local classification itself is independent
of these stronger nonmate assumptions. -/
theorem IsStarPacking.twoStarLeafSwap_admissible_new_bad_charge
    (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V)) (hCB : C ⊆ B)
    (hb : b ∈ C) (hc : c ∈ C) (hbc : b ≠ c)
    (hu : u ∈ L b) (hv : v ∈ L c) (hbv : G.Adj b v) (hcu : G.Adj c u)
    {q : ℝ} (hold : ∀ e ∈ C, MateFreeOn G q (↑(insert e (L e)) : Set V))
    (hpair : MateFreeOn G q (↑(insert b (L b) ∪ insert c (L c)) : Set V))
    (hdb : d ≠ b) (hdc : d ≠ c)
    (hnew : IsBadStarPair G (MinorFreeSpanners.twoStarLeafSwap L u v) b d)
    (hnot : ¬ IsBadStarPair G L b d) (hvd : ¬ G.Adj v d) :
    let M := MinorFreeSpanners.twoStarLeafSwap L u v
    IsStarPacking G A C ell M ∧
    (∀ e ∈ C, MateFreeOn G q (↑(insert e (M e)) : Set V)) ∧
    (∀ e ∈ C, ∀ f ∈ C, e ≠ f → Disjoint (insert e (M e)) (insert f (M f))) ∧
    (starCrossLeaves G L b d).card = 2 ∧
      ∃ w ∈ (L b).erase u, G.Adj u d ∧ G.Adj w d := by
  have hs := h.twoStarLeafSwap hG hCB hb hc hbc hu hv hbv hcu hold hpair
  exact ⟨hs.1,hs.2.2.2.2.1,hs.2.2.2.2.2,
    h.twoStarLeafSwap_new_bad_common_neighbor hbc hu hv hdb hdc hnew hnot hvd⟩

end MinorFreeSpanners
