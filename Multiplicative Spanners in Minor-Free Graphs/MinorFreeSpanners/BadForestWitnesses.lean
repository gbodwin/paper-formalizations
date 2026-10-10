import MinorFreeSpanners.MinimumBadStarFamily

/-! Compare bad pairs across an actual leaf swap using their forest edges,
not only their center labels. The finite edge-pair witness set has exactly
the already minimized ordered bad-center-pair count. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V : Type*}
attribute [local instance] Classical.propDecidable

structure BadLeafWitness (G : SimpleGraph V) (L : V → Finset V) (b c : V) where
  leftLeaf : V
  rightLeaf : V
  left_mem : leftLeaf ∈ L b
  right_mem : rightLeaf ∈ L c
  left_cross : G.Adj leftLeaf c
  right_cross : G.Adj rightLeaf b
  left_unique : ∀ x ∈ L b, G.Adj x c ↔ x=leftLeaf
  right_unique : ∀ y ∈ L c, G.Adj y b ↔ y=rightLeaf

noncomputable def chooseBadLeafWitness (G : SimpleGraph V) (L : V → Finset V)
    (b c : V) (h : IsBadStarPair G L b c) : BadLeafWitness G L b c :=
  Classical.choice (by
    obtain ⟨u,hu,v,hv,huc,hvb,hunique,hvunique⟩ := badStarPair_unique_leaves G L h
    exact ⟨⟨u,v,hu,hv,huc,hvb,hunique,hvunique⟩⟩)

noncomputable def badStarPairSet (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) : Finset (V×V) :=
  (C.product C).filter fun p => IsBadStarPair G L p.1 p.2

noncomputable def badForestWitness (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (p : badStarPairSet G C L) : (V×V)×(V×V) :=
  let w := chooseBadLeafWitness G L p.val.1 p.val.2 (Finset.mem_filter.mp p.property).2
  ((p.val.1,w.leftLeaf),(p.val.2,w.rightLeaf))

noncomputable def badForestPairs (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) : Finset ((V×V)×(V×V)) := by
  classical
  exact (badStarPairSet G C L).attach.image (badForestWitness G C L)

theorem badForestWitness_injective (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) : Function.Injective (badForestWitness G C L) := by
  intro p q he
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z : (V×V)×(V×V) => z.1.1) he)
    (congrArg (fun z : (V×V)×(V×V) => z.2.1) he)

/-- The real ordered forest-edge witnesses have precisely the minimized
score, with no multiplicity or factor-of-two change. -/
theorem badForestPairs_card (G : SimpleGraph V) (C : Finset V) (L : V → Finset V) :
    (badForestPairs G C L).card=badStarPairCount G C L := by
  classical
  rw [badForestPairs,Finset.card_image_of_injective _ (badForestWitness_injective G C L),
    Finset.card_attach]
  rfl

/-- Membership has actual leaf and cross-edge semantics, independently of
which canonical choice was used to represent the unique witnesses. -/
theorem mem_badForestPairs (G : SimpleGraph V) (C : Finset V) (L : V → Finset V)
    (b u c v : V) : ((b,u),(c,v)) ∈ badForestPairs G C L ↔
      b ∈ C ∧ c ∈ C ∧ IsBadStarPair G L b c ∧ u ∈ L b ∧ v ∈ L c ∧
        G.Adj u c ∧ G.Adj v b := by
  classical
  constructor
  · intro he
    obtain ⟨p,_,he⟩ := Finset.mem_image.mp he
    have hb : p.val.1=b := congrArg (fun z : (V×V)×(V×V) => z.1.1) he
    have hc : p.val.2=c := congrArg (fun z : (V×V)×(V×V) => z.2.1) he
    let w := chooseBadLeafWitness G L p.val.1 p.val.2 (Finset.mem_filter.mp p.property).2
    have hu : w.leftLeaf=u := congrArg (fun z : (V×V)×(V×V) => z.1.2) he
    have hv : w.rightLeaf=v := congrArg (fun z : (V×V)×(V×V) => z.2.2) he
    have hp := Finset.mem_filter.mp p.property
    have hpc := Finset.mem_product.mp hp.1
    exact ⟨hb ▸ hpc.1,hc ▸ hpc.2,by simpa only [hb,hc] using hp.2,
      by simpa only [hb,hu] using w.left_mem,
      by simpa only [hc,hv] using w.right_mem,
      by simpa only [hc,hu] using w.left_cross,
      by simpa only [hb,hv] using w.right_cross⟩
  · rintro ⟨hb,hc,hbad,hu,hv,huc,hvb⟩
    let p : badStarPairSet G C L := ⟨(b,c),Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hb,hc⟩,hbad⟩⟩
    let w := chooseBadLeafWitness G L b c hbad
    have hue : u=w.leftLeaf := (w.left_unique u hu).mp huc
    have hve : v=w.rightLeaf := (w.right_unique v hv).mp hvb
    apply Finset.mem_image.mpr
    refine ⟨p,Finset.mem_attach _ _,?_⟩
    change ((b,w.leftLeaf),(c,w.rightLeaf))=((b,u),(c,v))
    rw [hue,hve]

/-- On a genuine packing, both represented forest edges are actual host
edges, in addition to the two cross edges in the membership theorem. -/
theorem IsStarPacking.badForestPairs_actual_edges {G : SimpleGraph V}
    {A C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) {b u c v : V}
    (hp : ((b,u),(c,v)) ∈ badForestPairs G C L) :
    G.Adj b u ∧ G.Adj c v ∧ G.Adj u c ∧ G.Adj v b := by
  obtain ⟨_,_,_,hu,hv,huc,hvb⟩ := (mem_badForestPairs G C L b u c v).mp hp
  exact ⟨h.2.2.1 b u hu,h.2.2.1 c v hv,huc,hvb⟩

theorem badForestPairs_reverse {G : SimpleGraph V} {C : Finset V}
    {L : V → Finset V} {b u c v : V}
    (hp : ((b,u),(c,v)) ∈ badForestPairs G C L) :
    ((c,v),(b,u)) ∈ badForestPairs G C L := by
  obtain ⟨hb,hc,hbad,hu,hv,huc,hvb⟩ := (mem_badForestPairs G C L b u c v).mp hp
  exact (mem_badForestPairs G C L c v b u).mpr
    ⟨hc,hb,isBadStarPair_symm G L hbad,hv,hu,hvb,huc⟩

/-- The real bad neighboring centers incident through a specified leaf. -/
noncomputable def badLeafCenters (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (b u : V) : Finset V :=
  C.filter fun c => IsBadStarPair G L b c ∧ G.Adj u c

noncomputable def badForestOutgoing (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (b u : V) : Finset ((V×V)×(V×V)) :=
  (badForestPairs G C L).filter fun p => p.1=(b,u)

/-- Each genuine bad neighbor contributes exactly one outgoing ordered
forest-edge witness at the fixed edge. -/
theorem badForestOutgoing_card (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) {b u : V} (hb : b ∈ C) (hu : u ∈ L b) :
    (badForestOutgoing G C L b u).card=(badLeafCenters G C L b u).card := by
  classical
  apply Finset.card_bij (fun p _ => p.2.1)
  · intro p hp
    obtain ⟨hp,hpbu⟩ := Finset.mem_filter.mp hp
    rcases p with ⟨⟨a,x⟩,⟨c,v⟩⟩
    cases hpbu
    obtain ⟨_,hc,hbad,_,_,huc,_⟩ := (mem_badForestPairs G C L b u c v).mp hp
    exact Finset.mem_filter.mpr ⟨hc,hbad,huc⟩
  · intro p hp q hq he
    obtain ⟨hp,hpbu⟩ := Finset.mem_filter.mp hp
    obtain ⟨hq,hqbu⟩ := Finset.mem_filter.mp hq
    rcases p with ⟨⟨a,x⟩,⟨c,v⟩⟩
    rcases q with ⟨⟨a',x'⟩,⟨c',v'⟩⟩
    cases hpbu
    cases hqbu
    change c=c' at he
    subst c'
    obtain ⟨_,_,hbad,_,hv,_,hvb⟩ := (mem_badForestPairs G C L b u c v).mp hp
    obtain ⟨_,_,_,_,hv',_,hv'b⟩ := (mem_badForestPairs G C L b u c v').mp hq
    obtain ⟨_,_,w,_,_,_,_,hw⟩ := badStarPair_unique_leaves G L hbad
    have hvv' : v=v' := ((hw v hv).mp hvb).trans ((hw v' hv').mp hv'b).symm
    subst v'; rfl
  · intro c hc
    obtain ⟨hc,hbad,huc⟩ := Finset.mem_filter.mp hc
    obtain ⟨_,_,v,hv,_,hvb,_,_⟩ := badStarPair_unique_leaves G L hbad
    refine ⟨((b,u),(c,v)),Finset.mem_filter.mpr ⟨?_,rfl⟩,rfl⟩
    exact (mem_badForestPairs G C L b u c v).mpr ⟨hb,hc,hbad,hu,hv,huc,hvb⟩

/-- A true minimum of the old score forces at least as many newly created
actual witnesses as destroyed witnesses. This does not bound either side. -/
theorem badForestPairs_loss_le_gain (G : SimpleGraph V) (C : Finset V)
    (L M : V → Finset V) (hmin : badStarPairCount G C L ≤ badStarPairCount G C M) :
    (badForestPairs G C L \ badForestPairs G C M).card ≤
      (badForestPairs G C M \ badForestPairs G C L).card := by
  classical
  apply Finset.card_sdiff_le_card_sdiff_iff.mpr
  simpa only [badForestPairs_card] using hmin

end MinorFreeSpanners
