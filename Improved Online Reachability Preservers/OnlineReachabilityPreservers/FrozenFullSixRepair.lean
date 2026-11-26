import OnlineReachabilityPreservers.FrozenHalfFourConflicts

/-! An independent incidence selection within the original path budget. -/

namespace OnlineReachabilityPreservers

open Finset

section Retention

variable {A : Type*} [DecidableEq A]

/-- A set contains no pair linked by a directed conflict. -/
def CutConflictIndependent (edge : A → A → Prop) (keep : Finset A) : Prop :=
  ∀ ⦃a b⦄, a ∈ keep → b ∈ keep → ¬edge a b

variable {edge : A → A → Prop}

private noncomputable def cutNeighborhood (edge : A → A → Prop) (vertices : Finset A) (a : A) : Finset A := by
  classical
  exact vertices.filter (fun b => a = b ∨ edge a b ∨ edge b a)

private theorem mem_cutNeighborhood {vertices : Finset A} {a b : A} :
    b ∈ cutNeighborhood edge vertices a ↔ b ∈ vertices ∧ (a = b ∨ edge a b ∨ edge b a) := by
  classical
  exact mem_filter

private theorem cutNeighborhood_card_le_three
    (outgoing : ∀ {a b c}, edge a b → edge a c → b = c)
    (incoming : ∀ {a b c}, edge a b → edge c b → a = c)
    (vertices : Finset A) (a : A) : (cutNeighborhood edge vertices a).card ≤ 3 := by
  classical
  let following := vertices.filter (edge a)
  let previous := vertices.filter (fun b => edge b a)
  have followsAtMostOne : following.card ≤ 1 := card_le_one_iff.mpr fun b c =>
    outgoing (mem_filter.mp b).2 (mem_filter.mp c).2
  have priorAtMostOne : previous.card ≤ 1 := card_le_one_iff.mpr fun b c =>
    incoming (mem_filter.mp b).2 (mem_filter.mp c).2
  have inside : cutNeighborhood edge vertices a ⊆ {a} ∪ (following ∪ previous) := by
    intro b member
    rcases mem_cutNeighborhood.mp member with ⟨hb,eq | next | prior⟩
    · exact mem_union_left _ (mem_singleton.mpr eq.symm)
    · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hb,next⟩))
    · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hb,prior⟩))
  exact (card_le_card inside).trans ((card_union_le _ _).trans (by
    have rest := card_union_le following previous
    rw [card_singleton]
    omega))

/-- At most one edge of each orientation at every vertex gives an
independent set containing at least a third of any designated set. -/
theorem cutConflict_independent_third (vertices : Finset A) (loopless : ∀ a, ¬edge a a)
    (outgoing : ∀ {a b c}, edge a b → edge a c → b = c)
    (incoming : ∀ {a b c}, edge a b → edge c b → a = c) :
    ∃ keep ⊆ vertices, CutConflictIndependent edge keep ∧ vertices.card ≤ 3*keep.card := by
  classical
  induction vertices using Finset.strongInduction with
  | H vertices prior =>
    by_cases empty : vertices = ∅
    · subst vertices
      exact ⟨∅,Subset.rfl,(by intro a b ha; simp at ha),by simp⟩
    obtain ⟨a,memA⟩ := nonempty_iff_ne_empty.mpr empty
    let closed := cutNeighborhood edge vertices a
    let rest := vertices \ closed
    have inClosed : a ∈ closed := mem_cutNeighborhood.mpr ⟨memA,Or.inl rfl⟩
    have closedSub : closed ⊆ vertices := fun b member => (mem_cutNeighborhood.mp member).1
    have restSub : rest ⊆ vertices := sdiff_subset
    have proper : rest ⊂ vertices := Finset.ssubset_iff_subset_ne.mpr ⟨restSub,fun same => by
      have inRest : a ∈ rest := same.symm ▸ memA
      exact (mem_sdiff.mp inRest).2 inClosed⟩
    obtain ⟨keep,subset,independent,retained⟩ := prior rest proper
    have away (b : A) (inB : b ∈ keep) : a ≠ b ∧ ¬edge a b ∧ ¬edge b a := by
      have h := mem_sdiff.mp (subset inB)
      have no : ¬(a = b ∨ edge a b ∨ edge b a) := fun edge => h.2
        (mem_cutNeighborhood.mpr ⟨h.1,edge⟩)
      simpa only [not_or] using no
    have newIndependent : CutConflictIndependent edge (insert a keep) := by
      intro u v uIn vIn
      rcases mem_insert.mp uIn with rfl | onU <;> rcases mem_insert.mp vIn with rfl | onV
      · exact loopless _
      · exact (away _ onV).2.1
      · exact (away _ onU).2.2
      · exact independent onU onV
    have total := card_sdiff_add_card_eq_card closedSub
    change rest.card+closed.card = vertices.card at total
    have closedCount := cutNeighborhood_card_le_three (edge := edge) (fun {_ _ _} => outgoing)
      (fun {_ _ _} => incoming) vertices a
    have notKept : a ∉ keep := fun inside => (away a inside).1 rfl
    refine ⟨insert a keep,insert_subset memA (subset.trans restSub),newIndependent,?_⟩
    rw [card_insert_of_notMem notKept]
    change closed.card ≤ 3 at closedCount
    omega

/-- With all sources on heavy incidences, one independent set uses only
heavy incidences and another also keeps light incidences. Both preserve a
third of the heavy mass, with an additional contribution from isolated
heavy sources pointing at light targets. -/
theorem cutConflict_heavy_light_independent (heavy light : Finset A) (separate : Disjoint heavy light)
    (source : ∀ {a b}, edge a b → a ∈ heavy) (loopless : ∀ a, ¬edge a a)
    (outgoing : ∀ {a b c}, edge a b → edge a c → b = c)
    (incoming : ∀ {a b c}, edge a b → edge c b → a = c) :
    ∃ isolated : Finset A, ∃ onlyHeavy ⊆ heavy, ∃ mixHeavy ⊆ heavy, ∃ mixLight ⊆ light,
      CutConflictIndependent edge onlyHeavy ∧ CutConflictIndependent edge (mixHeavy ∪ mixLight) ∧
      heavy.card+2*isolated.card ≤ 3*onlyHeavy.card ∧
      heavy.card+2*isolated.card ≤ 3*mixHeavy.card ∧ light.card ≤ mixLight.card+isolated.card := by
  classical
  let cross := heavy.filter (fun a => ∃ b ∈ light, edge a b)
  let isolated := cross.filter (fun a => ¬∃ b, edge b a)
  let remainder := heavy \ isolated
  let roots := cross \ isolated
  have crossSub : cross ⊆ heavy := filter_subset _ _
  have isolatedSub : isolated ⊆ heavy := (filter_subset _ _).trans crossSub
  have noLinks (a : A) (inA : a ∈ isolated) (b : A) (inB : b ∈ heavy) : ¬edge a b ∧ ¬edge b a := by
    have noIncoming : ¬∃ c, edge c a := (mem_filter.mp inA).2
    obtain ⟨c,lightC,ac⟩ := (mem_filter.mp ((mem_filter.mp inA).1)).2
    exact ⟨fun ab => disjoint_left.mp separate ((outgoing ab ac) ▸ inB) lightC,
      fun ba => noIncoming ⟨b,ba⟩⟩
  have combine (vertices : Finset A) (sub : vertices ⊆ remainder)
      (legal : CutConflictIndependent edge vertices) : CutConflictIndependent edge (isolated ∪ vertices) := by
    intro a b memA memB
    rcases mem_union.mp memA with isoA | remA <;> rcases mem_union.mp memB with isoB | remB
    · exact (noLinks a isoA b (isolatedSub isoB)).1
    · exact (noLinks a isoA b (mem_sdiff.mp (sub remB)).1).1
    · exact (noLinks b isoB a (mem_sdiff.mp (sub remA)).1).2
    · exact legal remA remB
  have initialPartition : remainder.card+isolated.card = heavy.card :=
    card_sdiff_add_card_eq_card isolatedSub
  have unionCard (vertices : Finset A) (inside : vertices ⊆ remainder) :
      (isolated ∪ vertices).card = isolated.card+vertices.card :=
    card_union_of_disjoint (disjoint_left.mpr fun _ iso part => (mem_sdiff.mp (inside part)).2 iso)
  obtain ⟨greedy,greedySub,greedyFree,greedyCount⟩ :=
    cutConflict_independent_third (edge := edge) remainder loopless
      (fun {_ _ _} => outgoing) (fun {_ _ _} => incoming)
  let onlyHeavy := isolated ∪ greedy
  have onlySub : onlyHeavy ⊆ heavy := union_subset isolatedSub (greedySub.trans sdiff_subset)
  have onlyCount : heavy.card+2*isolated.card ≤ 3*onlyHeavy.card := by
    change _ ≤ 3*(isolated ∪ greedy).card
    rw [unionCard greedy greedySub]
    omega
  have aPredecessor (u : roots) : ∃ a, edge a u.val := by
    by_contra none
    obtain ⟨inCross,notIsolated⟩ := mem_sdiff.mp u.property
    exact notIsolated (mem_filter.mpr ⟨inCross,none⟩)
  let prev (u : roots) := (aPredecessor u).choose
  have prevEdge (u : roots) : edge (prev u) u.val := (aPredecessor u).choose_spec
  let anchors := roots.attach.image prev
  have anchorsSub : anchors ⊆ remainder := by
    intro a member
    obtain ⟨b,_,rfl⟩ := mem_image.mp member
    have inH := source (prevEdge b)
    have targetHeavy := crossSub (mem_sdiff.mp b.property).1
    exact mem_sdiff.mpr ⟨inH,fun iso => (noLinks _ iso _ targetHeavy).1 (prevEdge b)⟩
  have anchorsNotCross : Disjoint anchors cross := by
    apply disjoint_left.mpr
    intro a anchor crossed
    obtain ⟨b,_,rfl⟩ := mem_image.mp anchor
    obtain ⟨l,lightL,edgeL⟩ := (mem_filter.mp crossed).2
    have bHeavy := crossSub (mem_sdiff.mp b.property).1
    exact disjoint_left.mp separate ((outgoing (prevEdge b) edgeL) ▸ bHeavy) lightL
  have anchorsFree : CutConflictIndependent edge anchors := by
    intro a b anchorA anchorB ab
    obtain ⟨u,_,rfl⟩ := mem_image.mp anchorA
    have equal := outgoing (prevEdge u) ab
    exact disjoint_left.mp anchorsNotCross anchorB (equal ▸ (mem_sdiff.mp u.property).1)
  let removed := anchors.biUnion (cutNeighborhood edge remainder)
  have removedSub : removed ⊆ remainder := by
    intro u mem
    obtain ⟨_,_,neighbor⟩ := mem_biUnion.mp mem
    exact (mem_cutNeighborhood.mp neighbor).1
  have anchorsRemoved : anchors ⊆ removed := by
    exact fun a member => mem_biUnion.mpr ⟨a,member,mem_cutNeighborhood.mpr
      ⟨anchorsSub member,Or.inl rfl⟩⟩
  have rootsRemoved : roots ⊆ removed := by
    intro b inB
    let u : roots := ⟨b,inB⟩
    have anchor : prev u ∈ anchors := mem_image.mpr ⟨u,mem_attach _ _,rfl⟩
    have bRem : b ∈ remainder := by
      obtain ⟨inCross,notIso⟩ := mem_sdiff.mp inB
      exact mem_sdiff.mpr ⟨crossSub inCross,notIso⟩
    exact mem_biUnion.mpr ⟨prev u,anchor,mem_cutNeighborhood.mpr
      ⟨bRem,Or.inr (Or.inl (prevEdge u))⟩⟩
  have removedCap : removed.card ≤ 3*anchors.card := by
    calc
      _ ≤ ∑ a ∈ anchors, (cutNeighborhood edge remainder a).card := card_biUnion_le
      _ ≤ ∑ _a ∈ anchors, 3 := sum_le_sum fun a _ =>
        cutNeighborhood_card_le_three (edge := edge) (fun {_ _ _} => outgoing) (fun {_ _ _} => incoming) remainder a
      _ = _ := by simp [Nat.mul_comm]
  let untouched := remainder \ removed
  obtain ⟨other,otherSub,otherFree,otherCount⟩ :=
    cutConflict_independent_third (edge := edge) untouched loopless
      (fun {_ _ _} => outgoing) (fun {_ _ _} => incoming)
  have otherInRemainder : other ⊆ remainder := otherSub.trans sdiff_subset
  have anchorSeparate : Disjoint anchors other := disjoint_left.mpr fun _ a b =>
    (mem_sdiff.mp (otherSub b)).2 (anchorsRemoved a)
  have neither (a : A) (aIn : a ∈ anchors) (b : A) (bIn : b ∈ other) : ¬edge a b ∧ ¬edge b a := by
    have out : b ∉ removed := (mem_sdiff.mp (otherSub bIn)).2
    exact ⟨fun ab => out (mem_biUnion.mpr ⟨a,aIn,mem_cutNeighborhood.mpr
      ⟨otherInRemainder bIn,Or.inr (Or.inl ab)⟩⟩),
      fun ba => out (mem_biUnion.mpr ⟨a,aIn,mem_cutNeighborhood.mpr
        ⟨otherInRemainder bIn,Or.inr (Or.inr ba)⟩⟩)⟩
  let mixedRemainder := anchors ∪ other
  have mixedSub : mixedRemainder ⊆ remainder := union_subset anchorsSub otherInRemainder
  have mixedFree : CutConflictIndependent edge mixedRemainder := by
    intro a b memA memB
    rcases mem_union.mp memA with aAnchor | aOther <;> rcases mem_union.mp memB with bAnchor | bOther
    · exact anchorsFree aAnchor bAnchor
    · exact (neither a aAnchor b bOther).1
    · exact (neither b bAnchor a aOther).2
    · exact otherFree aOther bOther
  let mixHeavy := isolated ∪ mixedRemainder
  have mixHeavySub : mixHeavy ⊆ heavy := union_subset isolatedSub (mixedSub.trans sdiff_subset)
  have mixHeavyCount : heavy.card+2*isolated.card ≤ 3*mixHeavy.card := by
    have remainderPartition : untouched.card+removed.card = remainder.card :=
      card_sdiff_add_card_eq_card removedSub
    change _ ≤ 3*(isolated ∪ mixedRemainder).card
    rw [unionCard mixedRemainder mixedSub,show mixedRemainder.card = anchors.card+other.card from
      card_union_of_disjoint anchorSeparate]
    omega
  let dropped := isolated.biUnion (fun a => light.filter (edge a))
  have droppedSub : dropped ⊆ light := by
    intro a inside
    obtain ⟨_,_,member⟩ := mem_biUnion.mp inside
    exact (mem_filter.mp member).1
  have droppedCount : dropped.card ≤ isolated.card := by
    calc
      _ ≤ ∑ a ∈ isolated, (light.filter (edge a)).card := card_biUnion_le
      _ ≤ ∑ _a ∈ isolated, 1 := sum_le_sum fun _ _ => card_le_one_iff.mpr (fun {_ _} a b =>
        outgoing (mem_filter.mp a).2 (mem_filter.mp b).2)
      _ = _ := by simp
  let mixLight := light \ dropped
  have mixLightCount : light.card ≤ mixLight.card+isolated.card := by
    have part : mixLight.card+dropped.card = light.card := card_sdiff_add_card_eq_card droppedSub
    omega
  have outToLight {a b : A} (memA : a ∈ mixHeavy) (memB : b ∈ mixLight) (ab : edge a b) : False := by
    have bLight := (mem_sdiff.mp memB).1
    have aCross : a ∈ cross := mem_filter.mpr ⟨source ab,b,bLight,ab⟩
    rcases mem_union.mp memA with inIsolated | inRemainder
    · exact (mem_sdiff.mp memB).2
        (mem_biUnion.mpr ⟨a,inIsolated,mem_filter.mpr ⟨bLight,ab⟩⟩)
    · rcases mem_union.mp inRemainder with inAnchors | inOther
      · exact disjoint_left.mp anchorsNotCross inAnchors aCross
      · have inRoots : a ∈ roots := mem_sdiff.mpr ⟨aCross,(mem_sdiff.mp (otherInRemainder inOther)).2⟩
        exact (mem_sdiff.mp (otherSub inOther)).2 (rootsRemoved inRoots)
  have mixtureFree : CutConflictIndependent edge (mixHeavy ∪ mixLight) := by
    intro a b memA memB ab
    rcases mem_union.mp memA with heavyA | lightA
    · rcases mem_union.mp memB with heavyB | lightB
      · exact combine mixedRemainder mixedSub mixedFree heavyA heavyB ab
      · exact outToLight heavyA lightB ab
    · exact disjoint_left.mp separate (source ab) (mem_sdiff.mp lightA).1
  exact ⟨isolated,onlyHeavy,onlySub,mixHeavy,mixHeavySub,mixLight,sdiff_subset,
    combine greedy greedySub greedyFree,mixtureFree,onlyCount,mixHeavyCount,mixLightCount⟩

end Retention

section RowMass

variable {J V : Type*} [DecidableEq J] [DecidableEq V] [Fintype J] [Fintype V]

private theorem remainingIncidences_eq {pieces : J → List V} (rows : Finset J) (kept : Finset (J × V)) :
    pieceIncidences (erasePieceIncidences pieces (pieceIncidences pieces univ \ kept)) rows =
      pieceIncidences pieces rows ∩ kept := by
  ext a
  simp only [mem_pieceIncidences,mem_sdiff,mem_inter,mem_erasePieceIncidences,mem_univ,true_and]
  by_cases present : a.2 ∈ pieces a.1 <;> simp [present]

/-- Either the heavy pieces alone keep three tenths of the original mass,
or the repaired family keeps thirteen twenty-fifths within the full path budget. -/
theorem oppositeCut_repair_budget {p : ℕ} {pieces : J → List V} {edge : J × V → J × V → Prop}
    (simple : ∀ i, (pieces i).Nodup) (heavy light : Finset J) (separate : Disjoint heavy light)
    (coversRows : ∀ i, pieces i ≠ [] → i ∈ heavy ∪ light)
    (source : ∀ {a b}, edge a b → a ∈ pieceIncidences pieces heavy)
    (target : ∀ {a b}, edge a b → b ∈ pieceIncidences pieces univ)
    (loopless : ∀ a, ¬edge a a)
    (outgoing : ∀ {a b c}, edge a b → edge a c → b = c)
    (incoming : ∀ {a b c}, edge a b → edge c b → a = c)
    (heavyFits : heavy.card ≤ p) (lightRoom : 11*light.card ≤ 13*(p-heavy.card))
    (moderate : 50*(∑ i ∈ heavy, (pieces i).length) ≤ 29*(∑ i, (pieces i).length)) :
    ∃ (deleted : Finset (J × V)) (rows : Finset J),
      (∀ {a b}, edge a b → a ∈ deleted ∨ b ∈ deleted) ∧ rows.card ≤ p ∧
      ((rows = heavy ∧ 3*(∑ i, (pieces i).length) ≤ 10*(∑ i ∈ rows,
        (erasePieceIncidences pieces deleted i).length)) ∨
        13*(∑ i, (pieces i).length) ≤ 25*(∑ i ∈ rows, (erasePieceIncidences pieces deleted i).length)) := by
  classical
  let M := ∑ i, (pieces i).length
  let H := pieceIncidences pieces heavy
  let L := pieceIncidences pieces light
  let W := pieceIncidences pieces univ
  have Hcount : H.card = ∑ i ∈ heavy, (pieces i).length := pieceIncidences_card simple heavy
  have Wcount : W.card = M := pieceIncidences_card simple univ
  have Hinside : H ⊆ W := fun a member =>
    mem_pieceIncidences.mpr ⟨mem_univ _,(mem_pieceIncidences.mp member).2⟩
  have separated : Disjoint H L := disjoint_left.mpr fun _ onH onL =>
    disjoint_left.mp separate (mem_pieceIncidences.mp onH).1 (mem_pieceIncidences.mp onL).1
  have whole : H ∪ L = W := by
    ext a
    simp only [H,L,W,mem_union,mem_pieceIncidences,mem_univ,true_and]
    constructor
    · exact fun x => x.elim And.right And.right
    · intro present
      have notEmpty : pieces a.1 ≠ [] := by
        intro h
        simp [h] at present
      exact (mem_union.mp (coversRows _ notEmpty)).elim (fun a => Or.inl ⟨a,present⟩)
        (fun a => Or.inr ⟨a,present⟩)
  have total : H.card+L.card = M := by
    rw [← card_union_of_disjoint separated,whole,Wcount]
  have upperS : 50*H.card ≤ 29*M := Hcount.symm ▸ moderate
  have covers (keep : Finset (J × V)) (legal : CutConflictIndependent edge keep) :
      ∀ {a b}, edge a b → a ∈ W \ keep ∨ b ∈ W \ keep := by
    intro a b ab
    by_cases keepA : a ∈ keep
    · exact Or.inr (mem_sdiff.mpr ⟨target ab,fun keepB => legal keepA keepB ab⟩)
    · exact Or.inl (mem_sdiff.mpr ⟨Hinside (source ab),keepA⟩)
  have mass_after (keep : Finset (J × V)) (rows : Finset J) :
      (∑ i ∈ rows, (erasePieceIncidences pieces (W \ keep) i).length) =
        (pieceIncidences pieces rows ∩ keep).card := by
    have nodup (i : J) := (erasePieceIncidences_sublist pieces (W \ keep) i).nodup (simple i)
    rw [← pieceIncidences_card nodup rows,remainingIncidences_eq]
  obtain ⟨iso,only,onlySub,mixH,mixHSub,mixL,mixLSub,onlyFree,mixFree,
    onlyMass,mixHeavy,mixLight⟩ := cutConflict_heavy_light_independent (edge := edge) H L separated
      (fun {_ _} => source) loopless (fun {_ _ _} => outgoing) (fun {_ _ _} => incoming)
  by_cases enough : 3*M ≤ 10*only.card
  · refine ⟨W \ only,heavy,(fun {_ _} => covers only onlyFree),heavyFits,Or.inl ⟨rfl,?_⟩⟩
    rw [mass_after,inter_eq_right.mpr onlySub]
    exact enough
  let mix := mixH ∪ mixL
  let weight (i : J) := (erasePieceIncidences pieces (W \ mix) i).length
  have heavyMass : (∑ i ∈ heavy, weight i) = mixH.card := by
    rw [show (∑ i ∈ heavy, weight i) = _ from mass_after mix heavy]
    congr 1
    ext a
    constructor
    · intro h
      obtain ⟨aH,inside⟩ := mem_inter.mp h
      rcases mem_union.mp inside with aHeavy | aLight
      · exact aHeavy
      · exact (disjoint_left.mp separated aH (mixLSub aLight)).elim
    · intro h
      exact mem_inter.mpr ⟨mixHSub h,mem_union_left _ h⟩
  have lightMass : (∑ i ∈ light, weight i) = mixL.card := by
    rw [show (∑ i ∈ light, weight i) = _ from mass_after mix light]
    congr 1
    ext a
    constructor
    · intro h
      obtain ⟨aL,inside⟩ := mem_inter.mp h
      rcases mem_union.mp inside with aHeavy | aLight
      · exact (disjoint_left.mp separated (mixHSub aHeavy) aL).elim
      · exact aLight
    · intro h
      exact mem_inter.mpr ⟨mixLSub h,mem_union_right _ h⟩
  obtain ⟨keptLight,inside,count,keepMass⟩ :=
    trim_weights_ratio light weight (show 11 ≤ 13 by decide) lightRoom
  have disjoint := separate.mono_right inside
  let rows := heavy ∪ keptLight
  let K := ∑ i ∈ rows, weight i
  have howMany : rows.card ≤ p := by
    rw [show rows = heavy ∪ keptLight from rfl,card_union_of_disjoint disjoint]
    omega
  have massSplit : K = mixH.card+(∑ i ∈ keptLight, weight i) := by
    change (∑ i ∈ heavy ∪ keptLight, weight i) = _
    rw [sum_union disjoint,heavyMass]
  have improved : 39*K+20*H.card+7*iso.card ≥ 33*M := by
    rw [lightMass] at keepMass
    omega
  have cost : 25*(20*H.card+7*iso.card) ≤ 318*M := by omega
  refine ⟨W \ mix,rows,(fun {_ _} => covers mix mixFree),howMany,Or.inr ?_⟩
  change 13*M ≤ 25*K
  omega

end RowMass

end OnlineReachabilityPreservers
