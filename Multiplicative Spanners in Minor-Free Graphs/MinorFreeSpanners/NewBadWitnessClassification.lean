import MinorFreeSpanners.BadForestWitnesses
import MinorFreeSpanners.SwapBadPairCharge

/-! Actual new ordered forest-edge witnesses are localized at the exchanged
stars. When the witness avoids the inserted forest edge, the concrete
common-neighbor exception is necessary. No global count is assumed. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V : Type*}
attribute [local instance] Classical.propDecidable

/-- Membership depends only on the two actual owner leaf sets. -/
theorem badForestPairs_mem_of_owner_equal (G : SimpleGraph V) (C : Finset V)
    (L M : V → Finset V) {b u c v : V} (hb : M b=L b) (hc : M c=L c)
    (hp : ((b,u),(c,v)) ∈ badForestPairs G C M) :
    ((b,u),(c,v)) ∈ badForestPairs G C L := by
  obtain ⟨hbC,hcC,hbad,hu,hv,huc,hvb⟩ := (mem_badForestPairs G C M b u c v).mp hp
  exact (mem_badForestPairs G C L b u c v).mpr
    ⟨hbC,hcC,by simpa only [IsBadStarPair,starCrossLeaves,hb,hc] using hbad,
      hb ▸ hu,hc ▸ hv,huc,hvb⟩

/-- A genuinely new witness whose two leaves were already present cannot
have an old bad center pair: old badness would select this same unique pair. -/
theorem new_badForestPair_not_old_bad (G : SimpleGraph V) (C : Finset V)
    (L M : V → Finset V) {b u c v : V}
    (hp : ((b,u),(c,v)) ∈ badForestPairs G C M)
    (hn : ((b,u),(c,v)) ∉ badForestPairs G C L)
    (hu : u ∈ L b) (hv : v ∈ L c) : ¬ IsBadStarPair G L b c := by
  intro hbad
  obtain ⟨hb,hc,_,_,_,huc,hvb⟩ := (mem_badForestPairs G C M b u c v).mp hp
  exact hn ((mem_badForestPairs G C L b u c v).mpr ⟨hb,hc,hbad,hu,hv,huc,hvb⟩)

theorem IsStarPacking.new_badForestPair_changed_center
    {G : SimpleGraph V} {A C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) {b c u v d w e z : V}
    (hu : u ∈ L b) (hv : v ∈ L c)
    (hp : ((d,w),(e,z)) ∈ badForestPairs G C (MinorFreeSpanners.twoStarLeafSwap L u v))
    (hn : ((d,w),(e,z)) ∉ badForestPairs G C L) :
    d=b ∨ d=c ∨ e=b ∨ e=c := by
  by_contra he
  push Not at he
  exact hn (badForestPairs_mem_of_owner_equal G C L _
    (h.twoStarLeafSwap_at_other hu hv he.1 he.2.1)
    (h.twoStarLeafSwap_at_other hu hv he.2.2.1 he.2.2.2) hp)

/-- At the first changed owner and an unchanged third owner, an actual new
witness avoiding the inserted leaf lies in the previously proved finite
common-neighbor exception set. The explicit witness itself remains an old
leaf different from the removed one. -/
theorem IsStarPacking.new_badForestPair_no_inserted_charge
    {G : SimpleGraph V} {A C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) {b c u v d w z : V}
    (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c)
    (hdb : d ≠ b) (hdc : d ≠ c)
    (hp : ((b,w),(d,z)) ∈ badForestPairs G C (MinorFreeSpanners.twoStarLeafSwap L u v))
    (hn : ((b,w),(d,z)) ∉ badForestPairs G C L) (hwv : w ≠ v) :
    d ∈ swapNewBadNoInserted G L b c u v C ∧
      w ∈ (L b).erase u ∧ G.Adj u d ∧ G.Adj w d := by
  obtain ⟨_,hd,hbad,hw,hz,hwd,hzb⟩ :=
    (mem_badForestPairs G C _ b w d z).mp hp
  have hwold : w ∈ (L b).erase u := by
    rw [h.twoStarLeafSwap_at_left hbc hu hv] at hw
    exact (Finset.mem_insert.mp hw).resolve_left hwv
  have hzold : z ∈ L d := by
    simpa only [h.twoStarLeafSwap_at_other hu hv hdb hdc] using hz
  have hold := new_badForestPair_not_old_bad G C L _ hp hn (Finset.mem_erase.mp hwold).2 hzold
  have hvnew : v ∈ MinorFreeSpanners.twoStarLeafSwap L u v b := by
    rw [h.twoStarLeafSwap_at_left hbc hu hv]
    exact Finset.mem_insert_self _ _
  have hvd : ¬ G.Adj v d := by
    intro hvd
    obtain ⟨x,_,_,_,_,_,hx,_⟩ := badStarPair_unique_leaves G _ hbad
    exact hwv (((hx w hw).mp hwd).trans ((hx v hvnew).mp hvd).symm)
  obtain ⟨_,_,_,hud,_⟩ := h.twoStarLeafSwap_new_bad_common_neighbor hbc hu hv hdb hdc hbad hold hvd
  exact ⟨Finset.mem_filter.mpr ⟨hd,hdb,hdc,hbad,hold,hvd⟩,hwold,hud,hwd⟩

/-- On the actual ordered witness set, the two owner centers determine
both leaves uniquely. This is the injection needed for later finite counts. -/
theorem badForestPairs_eq_of_centers (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) {b u c v w z : V}
    (hp : ((b,u),(c,v)) ∈ badForestPairs G C L)
    (hq : ((b,w),(c,z)) ∈ badForestPairs G C L) : u=w ∧ v=z := by
  obtain ⟨_,_,hbad,hu,hv,huc,hvb⟩ := (mem_badForestPairs G C L b u c v).mp hp
  obtain ⟨_,_,_,hw,hz,hwc,hzb⟩ := (mem_badForestPairs G C L b w c z).mp hq
  obtain ⟨_,_,_,_,_,_,hx,hy⟩ := badStarPair_unique_leaves G L hbad
  exact ⟨((hx u hu).mp huc).trans ((hx w hw).mp hwc).symm,
    ((hy v hv).mp hvb).trans ((hy z hz).mp hzb).symm⟩

noncomputable def newNoInsertedWitnesses (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (b c u v : V) : Finset ((V×V)×(V×V)) :=
  (badForestPairs G C (MinorFreeSpanners.twoStarLeafSwap L u v) \ badForestPairs G C L).filter
    fun p => p.1.1=b ∧ p.2.1 ≠ b ∧ p.2.1 ≠ c ∧ p.1.2 ≠ v

/-- The exceptional ordered witnesses inject into their real third centers.
The finite exception count therefore bounds these actual new witnesses. -/
theorem IsStarPacking.newNoInsertedWitnesses_card_le
    {G : SimpleGraph V} {A C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) {b c u v : V}
    (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c) :
    (newNoInsertedWitnesses G C L b c u v).card ≤
      (swapNewBadNoInserted G L b c u v C).card := by
  classical
  let S := newNoInsertedWitnesses G C L b c u v
  let D := swapNewBadNoInserted G L b c u v C
  have him : ∀ p ∈ S, p.2.1 ∈ D := by
    intro p hp
    obtain ⟨hp,hb,hdb,hdc,hwv⟩ := Finset.mem_filter.mp hp
    obtain ⟨hnew,hold⟩ := Finset.mem_sdiff.mp hp
    rcases p with ⟨⟨a,w⟩,⟨d,z⟩⟩
    change a=b at hb
    subst a
    exact (h.new_badForestPair_no_inserted_charge hbc hu hv hdb hdc hnew hold hwv).1
  let f : S → D := fun p => ⟨p.val.2.1,him p.val p.property⟩
  have hinj : Function.Injective f := by
    intro p q he
    have hp := Finset.mem_filter.mp p.property
    have hq := Finset.mem_filter.mp q.property
    have hfirst : p.val.1.1=q.val.1.1 := hp.2.1.trans hq.2.1.symm
    have hsecond : p.val.2.1=q.val.2.1 := congrArg Subtype.val he
    have hmemP := (Finset.mem_sdiff.mp hp.1).1
    have hmemQ := (Finset.mem_sdiff.mp hq.1).1
    have hmemQ' : ((p.val.1.1,q.val.1.2),(p.val.2.1,q.val.2.2)) ∈
        badForestPairs G C (MinorFreeSpanners.twoStarLeafSwap L u v) := by
      simpa only [hfirst,hsecond] using hmemQ
    have hleaves := badForestPairs_eq_of_centers G C _ hmemP hmemQ'
    apply Subtype.ext
    exact Prod.ext (Prod.ext hfirst hleaves.1) (Prod.ext hsecond hleaves.2)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

/-- Actual new-witness counting inherits the old branch's genuine
common-neighbor threshold; no numerical surrogate replaces the graph. -/
theorem IsStarPacking.newNoInsertedWitnesses_card_le_mateFree [Fintype V]
    {G : SimpleGraph V} {A C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) {b c u v : V} {q : ℝ}
    (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c)
    (hfree : MateFreeOn G q (↑(insert b (L b)) : Set V)) :
    ((newNoInsertedWitnesses G C L b c u v).card:ℝ) ≤ ((L b).erase u).card*q :=
  (Nat.cast_le.mpr (h.newNoInsertedWitnesses_card_le hbc hu hv)).trans
    (h.swapNewBadNoInserted_card_le_mateFree hbc hu hv C hfree)

end MinorFreeSpanners
