import MinorFreeSpanners.BadForestWitnesses
import MinorFreeSpanners.TwoStarLeafSwap
import MinorFreeSpanners.UnmatedBadIncidence

/-! An actual leaf swap removes the fixed forest edge. Every old bad
neighbor through it destroys two distinct ordered edge-pair witnesses.
The genuine finite minimum then forces at least that many new witnesses.
This does not yet upper-bound the newly created witnesses. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V : Type*}
attribute [local instance] Classical.propDecidable

private theorem not_mem_badForestPairs_left (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) {b u : V} (hu : u ∉ L b)
    {p : (V×V)×(V×V)} (hp : p.1=(b,u)) : p ∉ badForestPairs G C L := by
  rcases p with ⟨⟨a,x⟩,⟨c,v⟩⟩
  cases hp
  intro he
  exact hu ((mem_badForestPairs G C L b u c v).mp he).2.2.2.1

/-- Exact finite loss lower bound, using the actual ordered witness sets. -/
theorem badForestPairs_loss_of_removed_leaf (G : SimpleGraph V) (C : Finset V)
    (L M : V → Finset V) {b u : V} (hb : b ∈ C) (hu : u ∈ L b)
    (hremoved : u ∉ M b) :
    2*(badLeafCenters G C L b u).card ≤
      (badForestPairs G C L \ badForestPairs G C M).card := by
  classical
  let S := badForestOutgoing G C L b u
  let T := S.image Prod.swap
  have hleft : S ⊆ badForestPairs G C L \ badForestPairs G C M := by
    intro p hp
    obtain ⟨hold,hpbu⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_sdiff.mpr ⟨hold,not_mem_badForestPairs_left G C M hremoved hpbu⟩
  have hright : T ⊆ badForestPairs G C L \ badForestPairs G C M := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have hl := hleft hq
    rcases q with ⟨⟨a,x⟩,⟨c,v⟩⟩
    refine Finset.mem_sdiff.mpr ⟨badForestPairs_reverse (Finset.mem_sdiff.mp hl).1,?_⟩
    intro hn
    exact (Finset.mem_sdiff.mp hl).2 (badForestPairs_reverse hn)
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro p hp hpt
    obtain ⟨q,hq,he⟩ := Finset.mem_image.mp hpt
    have hpf := (Finset.mem_filter.mp hp).2
    have hqf := (Finset.mem_filter.mp hq).2
    have hps : p.2=(b,u) := (congrArg Prod.snd he).symm.trans hqf
    have hold := (Finset.mem_filter.mp hp).1
    have heq : p=((b,u),(b,u)) := Prod.ext hpf hps
    rw [heq] at hold
    exact ((mem_badForestPairs G C L b u b u).mp hold).2.2.1.1 rfl
  have hcard : T.card=S.card := Finset.card_image_of_injective _
    (fun _ _ he => by simpa only [Prod.swap_swap] using congrArg Prod.swap he)
  have hle := Finset.card_le_card (Finset.union_subset hleft hright)
  rw [Finset.card_union_of_disjoint hd,hcard] at hle
  have hs : S.card=(badLeafCenters G C L b u).card := badForestOutgoing_card G C L hb hu
  rw [hs] at hle
  omega

/-- This uses the actual score comparison supplied by the previously
constructed finite minimizer, plus the literal leaf-swap operation. -/
theorem IsStarPacking.swap_new_witnesses {G : SimpleGraph V}
    {A C : Finset V} {ell : ℕ} {L : V → Finset V} {b c u v : V}
    (h : IsStarPacking G A C ell L) (hb : b ∈ C) (hbc : b ≠ c)
    (hu : u ∈ L b) (hv : v ∈ L c)
    (hmin : badStarPairCount G C L ≤
      badStarPairCount G C (MinorFreeSpanners.twoStarLeafSwap L u v)) :
    2*(badLeafCenters G C L b u).card ≤
      (badForestPairs G C (MinorFreeSpanners.twoStarLeafSwap L u v) \
        badForestPairs G C L).card := by
  classical
  have hremoved : u ∉ MinorFreeSpanners.twoStarLeafSwap L u v b := by
    rw [h.twoStarLeafSwap_at_left hbc hu hv]
    simp [h.swap_leaves_ne hbc hu hv]
  exact (badForestPairs_loss_of_removed_leaf G C L _ hb hu hremoved).trans
    (badForestPairs_loss_le_gain G C L _ hmin)

/-- Internally construct the finite minimum, then derive the witness gain
for every concrete admissible two-star exchange. No minimum-score oracle
is a hypothesis of this existence statement. -/
theorem exists_minimum_family_with_swap_witness_gain [Fintype V]
    (G : SimpleGraph V) (A B C : Finset V) (ell : ℕ) (q : ℝ)
    (L : V → Finset V) (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hL : IsStarPacking G A C ell L) (hfull : ∀ b ∈ C, (L b).card=ell)
    (hfree : ∀ b ∈ C, MateFreeOn G q (insert b (L b : Set V))) :
    ∃ M : V → Finset V,
      IsStarPacking G A C ell M ∧ (∀ b ∈ C, (M b).card=ell) ∧
      (∀ b ∈ C, MateFreeOn G q (insert b (M b : Set V))) ∧
      C.biUnion M=C.biUnion L ∧
      ∀ b ∈ C, ∀ c ∈ C, ∀ u ∈ M b, ∀ v ∈ M c, b ≠ c →
        G.Adj b v → G.Adj c u →
        MateFreeOn G q (↑(insert b (M b) ∪ insert c (M c)) : Set V) →
        2*(badLeafCenters G C M b u).card ≤
          (badForestPairs G C (twoStarLeafSwap M u v) \ badForestPairs G C M).card := by
  classical
  obtain ⟨M,hM,hMf,hMn,hcov,hmin⟩ :=
    exists_minimum_bad_star_family G A C ell q L hL hfull hfree
  refine ⟨M,hM,hMf,hMn,hcov,?_⟩
  intro b hb c hc u hu v hv hbc hbv hcu hpair
  apply hM.swap_new_witnesses hb hbc hu hv
  apply hmin
  · exact hM.twoStarLeafSwap_valid hG hu hv hbv hcu
  · intro d hd
    rw [twoStarLeafSwap_card]
    exact hMf d hd
  · simpa only [Finset.coe_insert] using hM.twoStarLeafSwap_mateFree hbc hu hv
      (by simpa only [Finset.coe_insert] using hMn) hpair
  · exact (twoStarLeafSwap_leaf_union hb hc hu hv).trans hcov

/-- An actual minimizing family supplies an admissible exchange for every
unmated bad neighbor through a given leaf, and forces twice the size of
that real incidence class among the newly created ordered witnesses. -/
theorem exists_family_with_unmated_swap_gain [Fintype V]
    (G : SimpleGraph V) (A B C : Finset V) (ell : ℕ) (q : ℝ)
    (L : V → Finset V) (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hL : IsStarPacking G A C ell L) (hfull : ∀ b ∈ C, (L b).card=ell)
    (hfree : ∀ b ∈ C, MateFreeOn G q (insert b (L b : Set V))) :
    ∃ M : V → Finset V,
      IsStarPacking G A C ell M ∧ (∀ b ∈ C, (M b).card=ell) ∧
      (∀ b ∈ C, MateFreeOn G q (insert b (M b : Set V))) ∧
      C.biUnion M=C.biUnion L ∧
      ∀ b ∈ C, ∀ u ∈ M b, ∀ c ∈ unmatedBadLeafCenters G q C M b u,
        ∃ v ∈ M c,
          IsStarPacking G A C ell (twoStarLeafSwap M u v) ∧
          (∀ d ∈ C, MateFreeOn G q (insert d (twoStarLeafSwap M u v d : Set V))) ∧
          2*(unmatedBadLeafCenters G q C M b u).card ≤
            (badForestPairs G C (twoStarLeafSwap M u v) \ badForestPairs G C M).card := by
  classical
  obtain ⟨M,hM,hMf,hMn,hcov,hgain⟩ :=
    exists_minimum_family_with_swap_witness_gain G A B C ell q L hG hL hfull hfree
  refine ⟨M,hM,hMf,hMn,hcov,?_⟩
  intro b hb u hu c hc
  obtain ⟨hc,huc⟩ := Finset.mem_filter.mp hc
  obtain ⟨hc,hbad,hn⟩ := Finset.mem_filter.mp hc
  obtain ⟨_,_,v,hv,_,hvb,_,_⟩ := badStarPair_unique_leaves G M hbad
  have hpair := not_matedStarCenters_union_mateFree G q C M hc hbad.1.symm hn
    (by simpa only [Finset.coe_insert] using hMn b hb)
    (by simpa only [Finset.coe_insert] using hMn c hc)
  refine ⟨v,hv,hM.twoStarLeafSwap_valid hG hu hv hvb.symm huc.symm,?_,?_⟩
  · simpa only [Finset.coe_insert] using hM.twoStarLeafSwap_mateFree hbad.1 hu hv
      (by simpa only [Finset.coe_insert] using hMn) hpair
  · have hsub : unmatedBadLeafCenters G q C M b u ⊆ badLeafCenters G C M b u := by
      intro d hd
      obtain ⟨hd,hud⟩ := Finset.mem_filter.mp hd
      obtain ⟨hd,hbad,_⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_filter.mpr ⟨hd,hbad,hud⟩
    exact (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)).trans
      (hgain b hb c hc u hu v hv hbad.1 hvb.symm huc.symm hpair)

end MinorFreeSpanners
