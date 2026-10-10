import MinorFreeSpanners.InsertedWitnessDegree
import MinorFreeSpanners.BadWitnessSwapLoss

/-! Cover every actual newly created ordered witness by an inserted-edge
charge or the genuine old-leaf common-neighbor exception, allowing reversal.
The resulting count keeps every class and the factor of two explicit. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V : Type*}
attribute [local instance] Classical.propDecidable

private theorem swap_assignment_comm (L : V → Finset V) (u v : V) :
    twoStarLeafSwap L v u=twoStarLeafSwap L u v := by
  funext d
  simp only [twoStarLeafSwap,Equiv.swap_comm v u]

/-- A new witness whose first owner is b either uses the inserted edge
(b,v), or is one of the actual exceptional third-center witnesses. -/
theorem IsStarPacking.new_witness_left_classes
    {G : SimpleGraph V} {A C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) {b c u v d w z : V}
    (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c)
    (hp : ((b,w),(d,z)) ∈ badForestPairs G C (MinorFreeSpanners.twoStarLeafSwap L u v))
    (hn : ((b,w),(d,z)) ∉ badForestPairs G C L) :
    ((b,w),(d,z)) ∈ badForestOutgoing G C (MinorFreeSpanners.twoStarLeafSwap L u v) b v ∨
      ((b,w),(d,z)) ∈ newNoInsertedWitnesses G C L b c u v := by
  classical
  by_cases hwv : w=v
  · exact Or.inl (Finset.mem_filter.mpr ⟨hp,by simp only [hwv]⟩)
  · right
    obtain ⟨_,_,hbad,hw,_,hwd,_⟩ := (mem_badForestPairs G C _ b w d z).mp hp
    have hdb : d ≠ b := hbad.1.symm
    have hdc : d ≠ c := by
      intro he
      subst d
      have hvnew : v ∈ MinorFreeSpanners.twoStarLeafSwap L u v b := by
        rw [h.twoStarLeafSwap_at_left hbc hu hv]
        exact Finset.mem_insert_self _ _
      obtain ⟨_,_,_,_,_,_,hf,_⟩ := badStarPair_unique_leaves G _ hbad
      exact hwv (((hf w hw).mp hwd).trans
        ((hf v hvnew).mp (h.2.2.1 c v hv).symm).symm)
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hp,hn⟩,rfl,hdb,hdc,hwv⟩

/-- All genuine new ordered witnesses lie in the four forward classes or
their reversals. No assumption that every new pair contains an inserted
forest edge is used. -/
theorem IsStarPacking.new_witness_cover
    {G : SimpleGraph V} {A C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) {b c u v : V}
    (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c) :
    let M := MinorFreeSpanners.twoStarLeafSwap L u v
    let Q := badForestOutgoing G C M b v ∪ badForestOutgoing G C M c u ∪
      newNoInsertedWitnesses G C L b c u v ∪ newNoInsertedWitnesses G C L c b v u
    badForestPairs G C M \ badForestPairs G C L ⊆ Q ∪ Q.image Prod.swap := by
  classical
  dsimp only
  let M := MinorFreeSpanners.twoStarLeafSwap L u v
  let Q := badForestOutgoing G C M b v ∪ badForestOutgoing G C M c u ∪
      newNoInsertedWitnesses G C L b c u v ∪ newNoInsertedWitnesses G C L c b v u
  have hforward : ∀ a w d z, a=b ∨ a=c →
      ((a,w),(d,z)) ∈ badForestPairs G C M →
      ((a,w),(d,z)) ∉ badForestPairs G C L → ((a,w),(d,z)) ∈ Q := by
    intro a w d z ha hp hn
    rcases ha with hab | hac
    · subst a
      rcases h.new_witness_left_classes hbc hu hv hp hn with hi | he
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hi))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ he)
    · subst a
      have hp' : ((c,w),(d,z)) ∈ badForestPairs G C (MinorFreeSpanners.twoStarLeafSwap L v u) := by
        rw [swap_assignment_comm]; exact hp
      rcases h.new_witness_left_classes hbc.symm hv hu hp' hn with hi | he
      · have hi' : ((c,w),(d,z)) ∈ badForestOutgoing G C M c u := by
          rw [swap_assignment_comm] at hi; exact hi
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hi'))
      · exact Finset.mem_union_right _ he
  intro p hp
  rcases p with ⟨⟨a,w⟩,⟨d,z⟩⟩
  obtain ⟨hnew,hold⟩ := Finset.mem_sdiff.mp hp
  rcases h.new_badForestPair_changed_center hu hv hnew hold with hb | hc | hd | he
  · exact Finset.mem_union_left _ (hforward _ _ _ _ (Or.inl hb) hnew hold)
  · exact Finset.mem_union_left _ (hforward _ _ _ _ (Or.inr hc) hnew hold)
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨((d,z),(a,w)),hforward _ _ _ _ (Or.inl hd) (badForestPairs_reverse hnew)
      (fun hr => hold (badForestPairs_reverse hr)),rfl⟩
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨((d,z),(a,w)),hforward _ _ _ _ (Or.inr he) (badForestPairs_reverse hnew)
      (fun hr => hold (badForestPairs_reverse hr)),rfl⟩

/-- The actual four-class cover gives a finite cardinality budget with the
ordered reversal factor kept explicit. -/
theorem IsStarPacking.new_witness_card_budget
    {G : SimpleGraph V} {A C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) {b c u v : V}
    (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c) :
    let M := MinorFreeSpanners.twoStarLeafSwap L u v
    (badForestPairs G C M \ badForestPairs G C L).card ≤
      2*((badForestOutgoing G C M b v).card+(badForestOutgoing G C M c u).card+
        (newNoInsertedWitnesses G C L b c u v).card+
        (newNoInsertedWitnesses G C L c b v u).card) := by
  classical
  dsimp only
  let S := badForestOutgoing G C (MinorFreeSpanners.twoStarLeafSwap L u v) b v
  let T := badForestOutgoing G C (MinorFreeSpanners.twoStarLeafSwap L u v) c u
  let E := newNoInsertedWitnesses G C L b c u v
  let F := newNoInsertedWitnesses G C L c b v u
  have hc := Finset.card_le_card (h.new_witness_cover hbc hu hv)
  have hcu := Finset.card_union_le (S ∪ T ∪ E ∪ F) ((S ∪ T ∪ E ∪ F).image Prod.swap)
  have hi := Finset.card_image_le (s:=S ∪ T ∪ E ∪ F) (f:=Prod.swap)
  have h1 := Finset.card_union_le S T
  have h2 := Finset.card_union_le (S ∪ T) E
  have h3 := Finset.card_union_le (S ∪ T ∪ E) F
  change (badForestPairs G C (MinorFreeSpanners.twoStarLeafSwap L u v) \ badForestPairs G C L).card ≤
    2*(S.card+T.card+E.card+F.card)
  change (badForestPairs G C (MinorFreeSpanners.twoStarLeafSwap L u v) \ badForestPairs G C L).card ≤
    ((S ∪ T ∪ E ∪ F) ∪ (S ∪ T ∪ E ∪ F).image Prod.swap).card at hc
  omega

/-- Combine actual induced-neighbor injections and original-host mate-free
exception counts. Every newly created ordered witness is accounted for,
including center pairs that remain bad but change their leaf witnesses. -/
theorem IsStarPacking.new_witness_induced_budget [Fintype V]
    {G : SimpleGraph V} {A B C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    {b c u v : V} (hb : b ∈ C) (hc : c ∈ C) (hbc : b ≠ c)
    (hu : u ∈ L b) (hv : v ∈ L c) (hbv : G.Adj b v) (hcu : G.Adj c u)
    (q : ℝ) (hq : 0 ≤ q)
    (hfb : MateFreeOn G q (↑(insert b (L b)) : Set V))
    (hfc : MateFreeOn G q (↑(insert c (L c)) : Set V)) :
    ((badForestPairs G C (MinorFreeSpanners.twoStarLeafSwap L u v) \ badForestPairs G C L).card:ℝ) ≤
      2*((G.induce (swapWitnessVertices G C L b u : Set V)).degree
          ⟨v,(swapWitnessVertices_partner_mem hc hv hcu).2⟩+
        ((G.induce (swapWitnessVertices G C L b u : Set V)).degree
          ⟨c,(swapWitnessVertices_partner_mem hc hv hcu).1⟩:ℝ)+2*ell*q) := by
  classical
  have hn := Nat.cast_le (α:=ℝ).mpr (h.new_witness_card_budget hbc hu hv)
  push_cast at hn
  have hl := Nat.cast_le (α:=ℝ).mpr (h.inserted_left_witness_count hb hc hbc hu hv hcu)
  have hr := Nat.cast_le (α:=ℝ).mpr (h.inserted_right_witness_count hG hb hc hbc hu hv hbv hcu)
  have he := h.newNoInsertedWitnesses_card_le_mateFree hbc hu hv hfb
  have hf := h.newNoInsertedWitnesses_card_le_mateFree hbc.symm hv hu hfc
  have hbsize : (((L b).erase u).card:ℝ) ≤ ell :=
    Nat.cast_le.mpr ((Finset.card_erase_le).trans (h.2.2.2.2.2 b))
  have hcsize : (((L c).erase v).card:ℝ) ≤ ell :=
    Nat.cast_le.mpr ((Finset.card_erase_le).trans (h.2.2.2.2.2 c))
  have heb := he.trans (mul_le_mul_of_nonneg_right hbsize hq)
  have hfc' := hf.trans (mul_le_mul_of_nonneg_right hcsize hq)
  nlinarith

/-- Internally select the true minimum family and obtain the actual induced
neighbor-degree lower bound for every unmated bad partner through a leaf.
No minimum oracle, new-witness estimate, or abstract induced graph is an
input. The later summation into a dense witness remains separate. -/
theorem exists_family_with_unmated_induced_degree_budget [Fintype V]
    (G : SimpleGraph V) (A B C : Finset V) (ell : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (L : V → Finset V) (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hL : IsStarPacking G A C ell L) (hfull : ∀ b ∈ C, (L b).card=ell)
    (hfree : ∀ b ∈ C, MateFreeOn G q (insert b (L b : Set V))) :
    ∃ M : V → Finset V,
      IsStarPacking G A C ell M ∧ (∀ b ∈ C, (M b).card=ell) ∧
      (∀ b ∈ C, MateFreeOn G q (insert b (M b : Set V))) ∧
      C.biUnion M=C.biUnion L ∧
      ∀ b ∈ C, ∀ u ∈ M b, ∀ c ∈ unmatedBadLeafCenters G q C M b u,
        ∃ v ∈ M c, G.Adj b v ∧ G.Adj c u ∧
          ∃ vv cc : (swapWitnessVertices G C M b u : Set V),
            vv.val=v ∧ cc.val=c ∧
            ((unmatedBadLeafCenters G q C M b u).card:ℝ) ≤
              (G.induce (swapWitnessVertices G C M b u : Set V)).degree vv+
              ((G.induce (swapWitnessVertices G C M b u : Set V)).degree cc:ℝ)+2*ell*q := by
  classical
  obtain ⟨M,hM,hMf,hMn,hcov,hgain⟩ :=
    exists_family_with_unmated_swap_gain G A B C ell q L hG hL hfull hfree
  refine ⟨M,hM,hMf,hMn,hcov,?_⟩
  intro b hb u hu c hc
  obtain ⟨v,hv,hN,_,hgainN⟩ := hgain b hb u hu c hc
  obtain ⟨hc,huc⟩ := Finset.mem_filter.mp hc
  obtain ⟨hc,hbad,_⟩ := Finset.mem_filter.mp hc
  have hvnew : v ∈ twoStarLeafSwap M u v b := by
    rw [hM.twoStarLeafSwap_at_left hbad.1 hu hv]
    exact Finset.mem_insert_self _ _
  have hbv := hN.2.2.1 b v hvnew
  have hcu := huc.symm
  refine ⟨v,hv,hbv,hcu,⟨v,(swapWitnessVertices_partner_mem hc hv hcu).2⟩,
    ⟨c,(swapWitnessVertices_partner_mem hc hv hcu).1⟩,rfl,rfl,?_⟩
  have hupper := hM.new_witness_induced_budget hG hb hc hbad.1 hu hv hbv hcu q hq
    (by simpa only [Finset.coe_insert] using hMn b hb)
    (by simpa only [Finset.coe_insert] using hMn c hc)
  have hlower := Nat.cast_le (α:=ℝ).mpr hgainN
  push_cast at hlower
  nlinarith

end MinorFreeSpanners
