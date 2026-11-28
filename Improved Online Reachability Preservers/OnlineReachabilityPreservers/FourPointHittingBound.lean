import OnlineReachabilityPreservers.CutConflictMatching

/-! A four-point hitting bound using pairings of intersecting constraints. -/

namespace OnlineReachabilityPreservers

open Finset

private def pairedSupport {B : Type*} [DecidableEq B] (matching : Finset (B × B)) : Finset B :=
  matching.biUnion cutEdgeEndpoints

private theorem mem_pairedSupport {B : Type*} [DecidableEq B] {matching : Finset (B × B)} {x : B} :
    x ∈ pairedSupport matching ↔ ∃ e ∈ matching, x ∈ cutEdgeEndpoints e := by
  exact mem_biUnion

private theorem pairedSupport_insert {B : Type*} [DecidableEq B] (matching : Finset (B × B)) (e : B × B) :
    pairedSupport (insert e matching) = cutEdgeEndpoints e ∪ pairedSupport matching := by
  ext x
  simp only [mem_pairedSupport,mem_insert,mem_union]
  constructor
  · rintro ⟨pair,rfl | old,member⟩
    · exact Or.inl member
    · exact Or.inr ⟨pair,old,member⟩
  · rintro (member | ⟨pair,old,member⟩)
    · exact ⟨e,Or.inl rfl,member⟩
    · exact ⟨pair,Or.inr old,member⟩

private theorem pairedSupport_mono {B : Type*} [DecidableEq B] {first second : Finset (B × B)}
    (nested : first ⊆ second) : pairedSupport first ⊆ pairedSupport second := by
  intro x member
  obtain ⟨e,pair,atEnd⟩ := mem_pairedSupport.mp member
  exact mem_pairedSupport.mpr ⟨e,nested pair,atEnd⟩

private theorem pairedSupport_subset {B : Type*} [DecidableEq B] {edge : B → B → Prop}
    {support : Finset B} {matching : Finset (B × B)} (matched : CutMatching edge support matching) :
    pairedSupport matching ⊆ support := by
  intro x hasPair
  obtain ⟨e,selected,atEnd⟩ := mem_pairedSupport.mp hasPair
  have member : x = e.1 ∨ x = e.2 := by simpa [cutEdgeEndpoints] using atEnd
  exact member.elim (fun eq => eq ▸ (matched.1 e selected).1) (fun eq => eq ▸ (matched.1 e selected).2.1)

private theorem pairedSupport_card {B : Type*} [DecidableEq B] {edge : B → B → Prop}
    {support : Finset B} {matching : Finset (B × B)} (matched : CutMatching edge support matching)
    (noLoops : ∀ {x y}, edge x y → x ≠ y) :
    (pairedSupport matching).card = 2*matching.card := by
  unfold pairedSupport
  rw [card_biUnion (fun _ sa _ sb ne => matched.2 _ sa _ sb ne)]
  calc
    _ = ∑ e ∈ matching, (2:ℕ) := by
      apply sum_congr rfl
      intro e eIn
      have apart := noLoops (matched.1 e eIn).2.2
      simp [cutEdgeEndpoints,apart]
    _ = _ := by simp [Nat.mul_comm]

private theorem pairing_insert {B : Type*} [DecidableEq B] {edge : B → B → Prop}
    {support : Finset B} {matching : Finset (B × B)} (matched : CutMatching edge support matching)
    (pair : B × B) (valid : pair.1 ∈ support ∧ pair.2 ∈ support ∧ edge pair.1 pair.2)
    (apart : Disjoint (cutEdgeEndpoints pair) (pairedSupport matching)) :
    CutMatching edge support (insert pair matching) ∧ (insert pair matching).card = matching.card+1 := by
  have fresh : pair ∉ matching := by
    intro old
    have atEnd : pair.1 ∈ cutEdgeEndpoints pair := by simp [cutEdgeEndpoints]
    exact disjoint_left.mp apart atEnd (mem_pairedSupport.mpr ⟨pair,old,atEnd⟩)
  refine ⟨⟨?_,?_⟩,card_insert_of_notMem fresh⟩
  · intro e member
    rcases mem_insert.mp member with rfl | old
    · exact valid
    · exact matched.1 e old
  · intro e eIn f fIn different
    rcases mem_insert.mp eIn with rfl | eOld
    · rcases mem_insert.mp fIn with rfl | fOld
      · exact (different rfl).elim
      · exact apart.mono_right (fun _ endOf => mem_pairedSupport.mpr ⟨f,fOld,endOf⟩)
    · rcases mem_insert.mp fIn with rfl | fOld
      · exact (apart.mono_right (fun _ endOf => mem_pairedSupport.mpr ⟨e,eOld,endOf⟩)).symm
      · exact matched.2 _ eOld _ fOld different

private theorem pairing_erase {B : Type*} [DecidableEq B] {edge : B → B → Prop}
    {support : Finset B} {matching : Finset (B × B)} (matched : CutMatching edge support matching) (pair : B × B) :
    CutMatching edge support (matching.erase pair) :=
  ⟨fun _ eIn => matched.1 _ (mem_erase.mp eIn).2,
    fun _ eIn _ fIn different => matched.2 _ (mem_erase.mp eIn).2 _ (mem_erase.mp fIn).2 different⟩

private theorem exists_maximum_pairing {B : Type*} [DecidableEq B]
    (edge : B → B → Prop) (support : Finset B) :
    ∃ matching, CutMatching edge support matching ∧
      ∀ other, CutMatching edge support other → other.card ≤ matching.card := by
  classical
  let choices := (support.product support).powerset.filter (CutMatching edge support)
  have empty : (∅ : Finset (B × B)) ∈ choices := by simp [choices,CutMatching]
  obtain ⟨best,eligible,maximum⟩ := exists_max_image choices card ⟨∅,empty⟩
  refine ⟨best,(mem_filter.mp eligible).2,?_⟩
  intro other matched
  have within : other ⊆ support.product support := by
    intro e member
    exact mem_product.mpr ⟨(matched.1 _ member).1,(matched.1 _ member).2.1⟩
  exact maximum other (mem_filter.mpr ⟨mem_powerset.mpr within,matched⟩)

private theorem pairing_no_free_pair {B : Type*} [DecidableEq B] {edge : B → B → Prop}
    {support : Finset B} {matching : Finset (B × B)} (matched : CutMatching edge support matching)
    (maximum : ∀ other, CutMatching edge support other → other.card ≤ matching.card)
    {a b : B} (aFree : a ∈ support \ pairedSupport matching) (bFree : b ∈ support \ pairedSupport matching) :
    ¬ edge a b := by
  intro adjacent
  have apart : Disjoint (cutEdgeEndpoints (a,b)) (pairedSupport matching) := by
    apply disjoint_left.mpr
    intro x endOf on
    rcases (show x = a ∨ x = b from by simpa [cutEdgeEndpoints] using endOf) with rfl | rfl
    · exact (mem_sdiff.mp aFree).2 on
    · exact (mem_sdiff.mp bFree).2 on
  obtain ⟨added,count⟩ := pairing_insert matched (a,b) ⟨(mem_sdiff.mp aFree).1,(mem_sdiff.mp bFree).1,adjacent⟩ apart
  have paid := maximum _ added
  omega

/-- Replacing one pair by two would beat the maximum if the endpoints
connect to two distinct unpaired elements. -/
private theorem pairing_no_augmenting_triple {B : Type*} [DecidableEq B] {edge : B → B → Prop}
    {support : Finset B} {matching : Finset (B × B)} (matched : CutMatching edge support matching)
    (maximum : ∀ other, CutMatching edge support other → other.card ≤ matching.card)
    (noLoops : ∀ {x y}, edge x y → x ≠ y)
    {e : B × B} (selected : e ∈ matching) {u v : B}
    (uFree : u ∈ support \ pairedSupport matching) (vFree : v ∈ support \ pairedSupport matching)
    (left : edge e.1 u) (right : edge e.2 v) : u = v := by
  by_contra different
  let rest := matching.erase e
  have onto : pairedSupport rest ⊆ pairedSupport matching := pairedSupport_mono (erase_subset _ _)
  have separate : Disjoint (cutEdgeEndpoints e) (pairedSupport rest) := by
    apply disjoint_left.mpr
    intro x on inRest
    obtain ⟨old,oldIn,endOf⟩ := mem_pairedSupport.mp inRest
    exact disjoint_left.mp (matched.2 e selected old (mem_erase.mp oldIn).2 (mem_erase.mp oldIn).1.symm) on endOf
  have e1 : e.1 ∈ cutEdgeEndpoints e := by simp [cutEdgeEndpoints]
  have e2 : e.2 ∈ cutEdgeEndpoints e := by simp [cutEdgeEndpoints]
  have notLeft : e.1 ∉ pairedSupport rest := disjoint_left.mp separate e1
  have notRight : e.2 ∉ pairedSupport rest := disjoint_left.mp separate e2
  have outLeft : u ∉ pairedSupport rest := fun on => (mem_sdiff.mp uFree).2 (onto on)
  have outRight : v ∉ pairedSupport rest := fun on => (mem_sdiff.mp vFree).2 (onto on)
  have leftApart : Disjoint (cutEdgeEndpoints (e.1,u)) (pairedSupport rest) := by
    simpa [cutEdgeEndpoints,disjoint_insert_left] using And.intro notLeft outLeft
  have rightApart : Disjoint (cutEdgeEndpoints (e.2,v)) (pairedSupport rest) := by
    simpa [cutEdgeEndpoints,disjoint_insert_left] using And.intro notRight outRight
  have crossLeft : e.2 ≠ u := by
    intro eq
    exact (mem_sdiff.mp uFree).2 (mem_pairedSupport.mpr ⟨e,selected,eq ▸ e2⟩)
  have crossRight : v ≠ e.1 := by
    intro eq
    exact (mem_sdiff.mp vFree).2 (mem_pairedSupport.mpr ⟨e,selected,eq.symm ▸ e1⟩)
  have bothApart : Disjoint (cutEdgeEndpoints (e.2,v)) (cutEdgeEndpoints (e.1,u)) := by
    have endApart : e.2 ≠ e.1 := (noLoops (matched.1 e selected).2.2).symm
    apply disjoint_left.mpr
    intro x first second
    simp only [cutEdgeEndpoints,mem_insert,mem_singleton] at first second
    rcases first with a | a <;> rcases second with b | b
    · exact endApart (a.symm.trans b)
    · exact crossLeft (a.symm.trans b)
    · exact crossRight (a.symm.trans b)
    · exact different (b.symm.trans a)
  let extended := insert (e.1,u) rest
  obtain ⟨first,firstSize⟩ := pairing_insert (pairing_erase matched e) (e.1,u)
    ⟨(matched.1 e selected).1,(mem_sdiff.mp uFree).1,left⟩ leftApart
  have fresh : Disjoint (cutEdgeEndpoints (e.2,v)) (pairedSupport extended) := by
    rw [show extended = _ from rfl,pairedSupport_insert,disjoint_union_right]
    exact ⟨bothApart,rightApart⟩
  obtain ⟨second,secondSize⟩ := pairing_insert first (e.2,v)
    ⟨(matched.1 e selected).2.1,(mem_sdiff.mp vFree).1,right⟩ fresh
  have estimate := maximum _ second
  have original : rest.card+1 = matching.card := card_erase_add_one selected
  dsimp only [extended,rest] at firstSize secondSize estimate original
  omega

private def intersectingConstraints {A : Type*} [DecidableEq A] (a b : Finset A) : Prop :=
  a ≠ b ∧ (a ∩ b).Nonempty

private def externalPairPoints {A : Type*} [DecidableEq A] (free : Finset (Finset A)) (pair : Finset A × Finset A) :
    Finset A :=
  (pair.1 ∪ pair.2) ∩ free.biUnion id

private theorem four_point_pair_external_card {A : Type*} [DecidableEq A]
    {family : Finset (Finset A)} {matching : Finset (Finset A × Finset A)}
    (sizes : ∀ edge ∈ family, edge.card = 4) (matched : CutMatching intersectingConstraints family matching)
    (largest : ∀ other, CutMatching intersectingConstraints family other → other.card ≤ matching.card)
    {pair : Finset A × Finset A} (selected : pair ∈ matching) :
    (externalPairPoints (family \ pairedSupport matching) pair).card ≤ 4 := by
  classical
  let free := family \ pairedSupport matching
  have firstUsed : pair.1 ∈ pairedSupport matching := mem_pairedSupport.mpr ⟨pair,selected,by simp [cutEdgeEndpoints]⟩
  have secondUsed : pair.2 ∈ pairedSupport matching := mem_pairedSupport.mpr ⟨pair,selected,by simp [cutEdgeEndpoints]⟩
  have edgeOf {a b : Finset A} (used : a ∈ pairedSupport matching) (available : b ∈ free) (common : (a ∩ b).Nonempty) :
      intersectingConstraints a b := ⟨fun eq => (mem_sdiff.mp available).2 (eq ▸ used),common⟩
  have forced {a b : Finset A} (aFree : a ∈ free) (bFree : b ∈ free)
      (first : (pair.1 ∩ a).Nonempty) (second : (pair.2 ∩ b).Nonempty) : a = b :=
    pairing_no_augmenting_triple matched largest (fun h => h.1) selected aFree bFree
      (edgeOf firstUsed aFree first) (edgeOf secondUsed bFree second)
  have atPoint {x : A} (external : x ∈ externalPairPoints free pair) :
      (x ∈ pair.1 ∨ x ∈ pair.2) ∧ ∃ a ∈ free, x ∈ a := by
    simpa only [externalPairPoints,mem_inter,mem_union,mem_biUnion,id_eq] using external
  by_cases first : ∃ a ∈ free, (pair.1 ∩ a).Nonempty
  · by_cases second : ∃ b ∈ free, (pair.2 ∩ b).Nonempty
    · obtain ⟨a,aFree,aEdge⟩ := first
      obtain ⟨b,bFree,bEdge⟩ := second
      have together := forced aFree bFree aEdge bEdge
      have inside : externalPairPoints free pair ⊆ a := by
        intro x external
        obtain ⟨one | two,c,cFree,cPoint⟩ := atPoint external
        · have collapse := forced cFree bFree ⟨x,mem_inter.mpr ⟨one,cPoint⟩⟩ bEdge
          exact (collapse.trans together.symm) ▸ cPoint
        · have collapse := forced aFree cFree aEdge ⟨x,mem_inter.mpr ⟨two,cPoint⟩⟩
          exact collapse.symm ▸ cPoint
      exact (card_le_card inside).trans_eq (sizes a (mem_sdiff.mp aFree).1)
    · have inside : externalPairPoints free pair ⊆ pair.1 := by
        intro x external
        obtain ⟨one | two,a,aFree,aPoint⟩ := atPoint external
        · exact one
        · exact (second ⟨a,aFree,x,mem_inter.mpr ⟨two,aPoint⟩⟩).elim
      exact (card_le_card inside).trans_eq (sizes _ (matched.1 pair selected).1)
  · have inside : externalPairPoints free pair ⊆ pair.2 := by
      intro x external
      obtain ⟨one | two,a,aFree,aPoint⟩ := atPoint external
      · exact (first ⟨a,aFree,x,mem_inter.mpr ⟨one,aPoint⟩⟩).elim
      · exact two
    exact (card_le_card inside).trans_eq (sizes _ (matched.1 pair selected).2.1)

private def incidentConstraints {A : Type*} [DecidableEq A] (family : Finset (Finset A)) (x : A) :
    Finset (Finset A) :=
  family.filter fun set => x ∈ set

private theorem incidentConstraints_sum_card {A : Type*} [DecidableEq A] (ground : Finset A)
    (family : Finset (Finset A)) (support : ∀ edge ∈ family, edge ⊆ ground) :
    (∑ x ∈ ground, (incidentConstraints family x).card) = ∑ edge ∈ family, edge.card := by
  calc
    _ = ∑ x ∈ ground, ∑ edge ∈ family, if x ∈ edge then (1:ℕ) else 0 := by
      simp only [incidentConstraints,card_filter]
    _ = ∑ edge ∈ family, ∑ x ∈ ground, if x ∈ edge then (1:ℕ) else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro edge edgeIn
      rw [← card_filter]
      have same : ground.filter (· ∈ edge) = edge := by
        ext x
        simp only [mem_filter,and_iff_right_iff_imp]
        exact fun atEdge => support edge edgeIn atEdge
      rw [same]

private def twoOwnerPoints {A : Type*} [DecidableEq A] (ground : Finset A) (family : Finset (Finset A)) : Finset A :=
  ground.filter fun x => (incidentConstraints family x).card = 2

private theorem twoOwnerPoints_has_two {A : Type*} [DecidableEq A] {ground : Finset A}
    {family : Finset (Finset A)} {x : A} (shared : x ∈ twoOwnerPoints ground family) :
    ∃ a b, a ≠ b ∧ incidentConstraints family x = {a,b} := card_eq_two.mp (mem_filter.mp shared).2

private theorem owner_of_mem {A : Type*} [DecidableEq A] {family : Finset (Finset A)} {x : A} {edge : Finset A}
    (owner : edge ∈ incidentConstraints family x) : edge ∈ family ∧ x ∈ edge := mem_filter.mp owner

private theorem four_point_sum_le_ground_add_shared {A : Type*} [DecidableEq A] (ground : Finset A)
    (family : Finset (Finset A)) (support : ∀ edge ∈ family, edge ⊆ ground)
    (sizes : ∀ edge ∈ family, edge.card = 4) (degree : ∀ x ∈ ground, (incidentConstraints family x).card ≤ 2) :
    4*family.card ≤ ground.card+(twoOwnerPoints ground family).card := by
  have charge (x : A) (xIn : x ∈ ground) :
      (incidentConstraints family x).card ≤ 1+(if x ∈ twoOwnerPoints ground family then 1 else 0) := by
    have upper := degree x xIn
    by_cases has : (incidentConstraints family x).card = 2
    · have member : x ∈ twoOwnerPoints ground family := mem_filter.mpr ⟨xIn,has⟩
      simp [has,member]
    · have small : (incidentConstraints family x).card ≤ 1 := by omega
      exact small.trans (Nat.le_add_right _ _)
  have countOwners : (∑ edge ∈ family, edge.card) = 4*family.card := calc
    _ = ∑ _ ∈ family, (4:ℕ) := sum_congr rfl sizes
    _ = _ := by simp [Nat.mul_comm]
  have visits := sum_le_sum (fun x xIn => charge x xIn)
  rw [incidentConstraints_sum_card ground family support,countOwners,sum_add_distrib] at visits
  have mark : (∑ x ∈ ground, if x ∈ twoOwnerPoints ground family then (1:ℕ) else 0) =
      (twoOwnerPoints ground family).card := by
    rw [← card_filter,filter_mem_eq_inter]
    exact congrArg card (inter_eq_right.mpr (filter_subset _ _))
  simpa only [sum_const,nsmul_eq_mul,Nat.cast_id,mul_one,mark] using visits

private theorem four_point_shared_card_le_six_matches {A : Type*} [DecidableEq A] (ground : Finset A)
    {family : Finset (Finset A)} {matching : Finset (Finset A × Finset A)}
    (support : ∀ edge ∈ family, edge ⊆ ground) (sizes : ∀ edge ∈ family, edge.card = 4)
    (matched : CutMatching intersectingConstraints family matching)
    (largest : ∀ other, CutMatching intersectingConstraints family other → other.card ≤ matching.card) :
    (twoOwnerPoints ground family).card ≤ 6*matching.card := by
  classical
  let used := pairedSupport matching
  let free := family \ used
  let shared := twoOwnerPoints ground family
  let crossing := shared.filter fun x => ∃ a ∈ free, x ∈ a
  have usedSubset : used ⊆ family := pairedSupport_subset matched
  have usedCard : used.card = 2*matching.card := pairedSupport_card matched (fun h => h.1)
  have countPairs {x : A} (xShared : x ∈ shared) :
      ∃ a b, a ≠ b ∧ a ∈ family ∧ x ∈ a ∧ b ∈ family ∧ x ∈ b := by
    obtain ⟨a,b,different,owners⟩ := twoOwnerPoints_has_two xShared
    have ownA : a ∈ incidentConstraints family x := by rw [owners]; simp
    have ownB : b ∈ incidentConstraints family x := by rw [owners]; simp
    obtain ⟨aIn,ax⟩ := owner_of_mem ownA
    obtain ⟨bIn,bx⟩ := owner_of_mem ownB
    exact ⟨a,b,different,aIn,ax,bIn,bx⟩
  have usedOwner {x : A} (xShared : x ∈ shared) : ∃ a ∈ used, x ∈ a := by
    obtain ⟨a,b,different,aIn,ax,bIn,bx⟩ := countPairs xShared
    by_cases au : a ∈ used
    · exact ⟨a,au,ax⟩
    · by_cases bu : b ∈ used
      · exact ⟨b,bu,bx⟩
      · have aFree : a ∈ free := mem_sdiff.mpr ⟨aIn,au⟩
        have bFree : b ∈ free := mem_sdiff.mpr ⟨bIn,bu⟩
        exact (pairing_no_free_pair matched largest aFree bFree ⟨different,⟨x,mem_inter.mpr ⟨ax,bx⟩⟩⟩).elim
  have crosses : crossing ⊆ matching.biUnion (externalPairPoints free) := by
    intro x xCrosses
    obtain ⟨xShared,a,aFree,ax⟩ := mem_filter.mp xCrosses
    obtain ⟨b,bUsed,bx⟩ := usedOwner xShared
    obtain ⟨pair,selected,atEnd⟩ := mem_pairedSupport.mp bUsed
    have inPair : x ∈ pair.1 ∪ pair.2 := by
      rcases (show b = pair.1 ∨ b = pair.2 from by simpa [cutEdgeEndpoints] using atEnd) with rfl | rfl
      · exact mem_union_left _ bx
      · exact mem_union_right _ bx
    exact mem_biUnion.mpr ⟨pair,selected,
      mem_inter.mpr ⟨inPair,mem_biUnion.mpr ⟨a,aFree,ax⟩⟩⟩
  have crossCard : crossing.card ≤ 4*matching.card := calc
    _ ≤ (matching.biUnion (externalPairPoints free)).card := card_le_card crosses
    _ ≤ ∑ pair ∈ matching, (externalPairPoints free pair).card := card_biUnion_le
    _ ≤ ∑ _ ∈ matching, (4:ℕ) := sum_le_sum (fun _ selected => four_point_pair_external_card sizes matched largest selected)
    _ = _ := by simp [Nat.mul_comm]
  have visitCounts (x : A) (xShared : x ∈ shared) :
      2 ≤ (incidentConstraints used x).card+(if x ∈ crossing then 1 else 0) := by
    by_cases externally : x ∈ crossing
    · obtain ⟨b,bUsed,bx⟩ := usedOwner xShared
      have paid := card_pos.mpr (show (incidentConstraints used x).Nonempty from ⟨b,mem_filter.mpr ⟨bUsed,bx⟩⟩)
      simp only [externally,ite_true]
      omega
    · obtain ⟨a,b,different,aIn,ax,bIn,bx⟩ := countPairs xShared
      have every {c : Finset A} (cIn : c ∈ family) (cx : x ∈ c) : c ∈ incidentConstraints used x := by
        apply mem_filter.mpr
        refine ⟨?_,cx⟩
        by_contra unpaired
        exact externally (mem_filter.mpr ⟨xShared,c,mem_sdiff.mpr ⟨cIn,unpaired⟩,cx⟩)
      have both : ({a,b} : Finset (Finset A)) ⊆ incidentConstraints used x := by
        intro c cIn
        rcases (show c = a ∨ c = b from by simpa using cIn) with rfl | rfl
        · exact every aIn ax
        · exact every bIn bx
      have paid : 2 ≤ (incidentConstraints used x).card := by
        simpa [different] using card_le_card both
      simpa only [externally,ite_false,Nat.add_zero] using paid
  have visits := sum_le_sum (fun x xIn => visitCounts x xIn)
  rw [sum_add_distrib] at visits
  have counted : (∑ x ∈ shared, if x ∈ crossing then (1:ℕ) else 0) = crossing.card := by
    rw [← card_filter,filter_mem_eq_inter]
    exact congrArg card (inter_eq_right.mpr (filter_subset _ _))
  have pairVisits : (∑ x ∈ ground, (incidentConstraints used x).card) = 8*matching.card := calc
    _ = ∑ edge ∈ used, edge.card := incidentConstraints_sum_card ground used (fun edge edgeIn => support edge (usedSubset edgeIn))
    _ = ∑ _ ∈ used, (4:ℕ) := sum_congr rfl (fun edge edgeIn => sizes edge (usedSubset edgeIn))
    _ = _ := by simp [usedCard,Nat.mul_assoc]; omega
  have limited : (∑ x ∈ shared, (incidentConstraints used x).card) ≤ ∑ x ∈ ground, (incidentConstraints used x).card :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  rw [pairVisits] at limited
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,counted] at visits
  change shared.card ≤ 6*matching.card
  omega

private theorem four_point_hit_of_matching {A : Type*} [DecidableEq A] (ground : Finset A)
    {family : Finset (Finset A)} {matching : Finset (Finset A × Finset A)}
    (support : ∀ edge ∈ family, edge ⊆ ground) (sizes : ∀ edge ∈ family, edge.card = 4)
    (matched : CutMatching intersectingConstraints family matching) :
    ∃ chosen ⊆ ground, (∀ edge ∈ family, (edge ∩ chosen).Nonempty) ∧
      chosen.card+matching.card ≤ family.card := by
  classical
  let used := pairedSupport matching
  let free := family \ used
  have usedSubset : used ⊆ family := pairedSupport_subset matched
  have usedCard : used.card = 2*matching.card := pairedSupport_card matched (fun h => h.1)
  have pairMeets (e : matching) : (e.val.1 ∩ e.val.2).Nonempty := (matched.1 _ e.property).2.2.2
  have freeMeets (edge : free) : edge.val.Nonempty :=
    card_pos.mp (by rw [sizes _ (mem_sdiff.mp edge.property).1]; decide)
  let pickPair (e : matching) := (pairMeets e).choose
  let pickFree (edge : free) := (freeMeets edge).choose
  let usedPoints := (univ : Finset matching).image pickPair
  let freePoints := (univ : Finset free).image pickFree
  let chosen := usedPoints ∪ freePoints
  have pairHere (e : matching) : (pickPair e) ∈ e.val.1 ∩ e.val.2 := (pairMeets e).choose_spec
  have freeHere (edge : free) : (pickFree edge) ∈ edge.val := (freeMeets edge).choose_spec
  have pairOn (e : matching) : pickPair e ∈ chosen := mem_union_left _
    (mem_image.mpr ⟨e,mem_univ _,rfl⟩)
  have freeOn (edge : free) : pickFree edge ∈ chosen := mem_union_right _
    (mem_image.mpr ⟨edge,mem_univ _,rfl⟩)
  have maxUsed : usedPoints.card ≤ matching.card := by
    simpa only [card_univ,Fintype.card_coe] using (card_image_le (s := (univ : Finset matching)) (f := pickPair))
  have maxFree : freePoints.card ≤ free.card := by
    simpa only [card_univ,Fintype.card_coe] using (card_image_le (s := (univ : Finset free)) (f := pickFree))
  have partitions : free.card+used.card = family.card := card_sdiff_add_card_eq_card usedSubset
  refine ⟨chosen,?_,?_,?_⟩
  · intro x member
    rcases mem_union.mp member with paired | alone
    · obtain ⟨e,_,rfl⟩ := mem_image.mp paired
      exact support _ (matched.1 e.val e.property).1 (mem_inter.mp (pairHere e)).1
    · obtain ⟨e,_,rfl⟩ := mem_image.mp alone
      exact support _ (mem_sdiff.mp e.property).1 (freeHere e)
  · intro e eIn
    by_cases eUsed : e ∈ used
    · obtain ⟨pair,selected,place⟩ := mem_pairedSupport.mp eUsed
      let picked : matching := ⟨pair,selected⟩
      rcases (show e = pair.1 ∨ e = pair.2 from by simpa [cutEdgeEndpoints] using place) with rfl | rfl
      · exact ⟨pickPair picked,mem_inter.mpr ⟨(mem_inter.mp (pairHere picked)).1,pairOn picked⟩⟩
      · exact ⟨pickPair picked,mem_inter.mpr ⟨(mem_inter.mp (pairHere picked)).2,pairOn picked⟩⟩
    · let alone : free := ⟨e,mem_sdiff.mpr ⟨eIn,eUsed⟩⟩
      exact ⟨pickFree alone,mem_inter.mpr ⟨freeHere alone,freeOn alone⟩⟩
  · have cap := card_union_le usedPoints freePoints
    dsimp only [chosen]
    omega

/-- A four-uniform family with `E` edges on `M` points has a hitting set
of size `S` with `6S ≤ M+2E` and `15S ≤ 3M+4E`. At incidence degree at
most two, take a maximum matching of intersecting edges. Any matched
pair meets the unpaired edges at no more than four distinct points. Connections from its two
endpoints to distinct unpaired sets would give an augmenting path. -/
theorem four_point_hitting_set_card_paired {A : Type*} [DecidableEq A] (ground : Finset A)
    (family : Finset (Finset A)) (support : ∀ edge ∈ family, edge ⊆ ground)
    (sizes : ∀ edge ∈ family, edge.card = 4) :
    ∃ chosen ⊆ ground, (∀ edge ∈ family, (edge ∩ chosen).Nonempty) ∧
      6*chosen.card ≤ 2*family.card+ground.card ∧
      15*chosen.card ≤ 4*family.card+3*ground.card := by
  classical
  induction size : family.card using Nat.strong_induction_on generalizing ground family with
  | h size ih =>
    by_cases heavy : ∃ x ∈ ground, 3 ≤ (incidentConstraints family x).card
    · obtain ⟨x,xIn,large⟩ := heavy
      let through := incidentConstraints family x
      let rest := family \ through
      have inside : through ⊆ family := filter_subset _ _
      have partition : rest.card+through.card = family.card := card_sdiff_add_card_eq_card inside
      change 3 ≤ through.card at large
      have smaller : rest.card < family.card := by omega
      have noPoint {edge} (insideRest : edge ∈ rest) : x ∉ edge :=
        fun h => (mem_sdiff.mp insideRest).2 (mem_filter.mpr ⟨(mem_sdiff.mp insideRest).1,h⟩)
      have remainder : ∀ edge ∈ rest, edge ⊆ ground.erase x := by
        intro edge edgeIn y atEdge
        have avoid : y ≠ x := fun eq => noPoint edgeIn (eq ▸ atEdge)
        exact mem_erase.mpr ⟨avoid,support edge (mem_sdiff.mp edgeIn).1 atEdge⟩
      obtain ⟨chosen,contained,covers,paidSix,paidFifteen⟩ := ih rest.card (by omega) (ground.erase x) rest remainder
        (fun edge edgeIn => sizes _ (mem_sdiff.mp edgeIn).1) rfl
      have fresh : x ∉ chosen := fun xChosen => notMem_erase x ground (contained xChosen)
      refine ⟨insert x chosen,insert_subset_iff.mpr ⟨xIn,contained.trans (erase_subset _ _)⟩,?_,?_⟩
      · intro edge edgeIn
        by_cases withPoint : x ∈ edge
        · exact ⟨x,mem_inter.mpr ⟨withPoint,mem_insert_self _ _⟩⟩
        · have edgeRest : edge ∈ rest :=
            mem_sdiff.mpr ⟨edgeIn,fun on => withPoint (owner_of_mem on).2⟩
          obtain ⟨y,hit⟩ := covers edge edgeRest
          exact ⟨y,mem_inter.mpr ⟨(mem_inter.mp hit).1,mem_insert_of_mem (mem_inter.mp hit).2⟩⟩
      · rw [card_insert_of_notMem fresh]
        have charge := card_erase_add_one xIn
        constructor <;> omega
    · have limited (x : A) (xIn : x ∈ ground) : (incidentConstraints family x).card ≤ 2 := by
        by_contra! higher
        exact heavy ⟨x,xIn,by omega⟩
      obtain ⟨matching,matched,largest⟩ := exists_maximum_pairing intersectingConstraints family
      obtain ⟨chosen,contained,covers,paid⟩ := four_point_hit_of_matching ground support sizes matched
      have twice := four_point_sum_le_ground_add_shared ground family support sizes limited
      have matchedTwice := four_point_shared_card_le_six_matches ground support sizes matched largest
      have fewShared : (twoOwnerPoints ground family).card ≤ ground.card := card_le_card (filter_subset _ _)
      have paidSix : 6*chosen.card ≤ 2*family.card+ground.card := by omega
      exact ⟨chosen,contained,covers,by omega,by omega⟩

end OnlineReachabilityPreservers
