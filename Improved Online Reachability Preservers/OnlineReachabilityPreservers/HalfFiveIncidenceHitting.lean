import OnlineReachabilityPreservers.FourPointHittingBound
import OnlineReachabilityPreservers.FrozenHalfFourConflicts
import OnlineReachabilityPreservers.LiteralFrozenHalfFive

/-! Four-incidence hitting sets for two-vertex intersections. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- A family of four-point subsets has a hitting set of size at most
three sevenths of the number of sets plus one seventh of the ground set. -/
theorem four_point_hitting_set_card {A : Type*} [DecidableEq A] (ground : Finset A)
    (family : Finset (Finset A)) (within : ∀ edge ∈ family, edge ⊆ ground)
    (sizes : ∀ edge ∈ family, edge.card = 4) :
    ∃ chosen ⊆ ground, (∀ edge ∈ family, (edge ∩ chosen).Nonempty) ∧
      7*chosen.card ≤ 3*family.card+ground.card := by
  classical
  induction size : family.card using Nat.strong_induction_on generalizing family ground with
  | h size ih =>
    by_cases overlap : ∃ a ∈ family, ∃ b ∈ family, a ≠ b ∧ ¬ Disjoint a b
    · obtain ⟨a,aIn,b,bIn,apart,common⟩ := overlap
      obtain ⟨x,ax,bx⟩ := not_disjoint_iff.mp common
      have xIn := within a aIn ax
      let rest := family.filter fun edge => x ∉ edge
      have fitted : rest ⊆ (family.erase a).erase b := by
        intro edge member
        obtain ⟨edgeIn,avoids⟩ := mem_filter.mp member
        have neA : edge ≠ a := by rintro rfl; exact avoids ax
        have neB : edge ≠ b := by rintro rfl; exact avoids bx
        exact mem_erase.mpr ⟨neB,mem_erase.mpr ⟨neA,edgeIn⟩⟩
      have smaller := card_le_card fitted
      have bStill : b ∈ family.erase a := mem_erase.mpr ⟨apart.symm,bIn⟩
      have nA := card_erase_add_one aIn
      have nB := card_erase_add_one bStill
      have nX := card_erase_add_one xIn
      obtain ⟨chosen,supported,hits,count⟩ := ih rest.card (by omega) (ground.erase x) rest
        (fun edge member z zIn => mem_erase.mpr ⟨fun same => (mem_filter.mp member).2 (same ▸ zIn),
          within edge (mem_filter.mp member).1 zIn⟩)
        (fun edge member => sizes edge (mem_filter.mp member).1) rfl
      have fresh : x ∉ chosen := fun xChosen => (mem_erase.mp (supported xChosen)).1 rfl
      refine ⟨insert x chosen,insert_subset_iff.mpr ⟨xIn,supported.trans (erase_subset _ _)⟩,?_,?_⟩
      · intro edge edgeIn
        by_cases carries : x ∈ edge
        · exact ⟨x,mem_inter.mpr ⟨carries,mem_insert_self _ _⟩⟩
        · obtain ⟨y,member⟩ := hits edge (mem_filter.mpr ⟨edgeIn,carries⟩)
          exact ⟨y,mem_inter.mpr ⟨(mem_inter.mp member).1,mem_insert_of_mem (mem_inter.mp member).2⟩⟩
      · rw [card_insert_of_notMem fresh]
        omega
    · have apart : (family : Set (Finset A)).PairwiseDisjoint id := by
        intro a aIn b bIn ne
        by_contra bad
        exact overlap ⟨a,aIn,b,bIn,ne,bad⟩
      have packed : family.biUnion id ⊆ ground := by
        intro x member
        obtain ⟨edge,edgeIn,point⟩ := mem_biUnion.mp member
        exact within edge edgeIn point
      have bound := card_le_card packed
      rw [card_biUnion apart] at bound
      have cardinal : (∑ edge ∈ family, (id edge).card) = 4*family.card := calc
        _ = ∑ _ ∈ family, (4:ℕ) := sum_congr rfl sizes
        _ = _ := by simp [Nat.mul_comm]
      rw [cardinal] at bound
      have nonempty (edge : family) : edge.val.Nonempty := card_pos.mp (by rw [sizes _ edge.property]; decide)
      let select (edge : family) := (nonempty edge).choose
      let chosen := (univ : Finset family).image select
      have membership (edge : family) : select edge ∈ edge.val := (nonempty edge).choose_spec
      have chosenSize : chosen.card ≤ family.card := by
        simpa only [card_univ,Fintype.card_coe] using
          (card_image_le : ((univ : Finset family).image select).card ≤ (univ : Finset family).card)
      refine ⟨chosen,?_,?_,by omega⟩
      · intro x contained
        obtain ⟨edge,_,rfl⟩ := mem_image.mp contained
        exact within _ edge.property (membership edge)
      · intro edge edgeIn
        let label : family := ⟨edge,edgeIn⟩
        exact ⟨select label,mem_inter.mpr ⟨membership label,mem_image.mpr ⟨label,mem_univ _,rfl⟩⟩⟩

private def increasingRowPairs (p : ℕ) : Finset (Fin p × Fin p) :=
  univ.filter fun pair => pair.1 < pair.2

private def commonRowPoints {n p : ℕ} (paths : Fin p → List (Fin n))
    (pair : Fin p × Fin p) : Finset (Fin n) :=
  (paths pair.1).toFinset ∩ (paths pair.2).toFinset

/-- For each unordered row pair count all unordered pairs of common vertices. -/
def commonVertexPairCount {n p : ℕ} (paths : Fin p → List (Fin n)) : ℕ :=
  ∑ pair ∈ increasingRowPairs p, (commonRowPoints paths pair).card.choose 2

private def commonPairIncidences {n p : ℕ} (pair : Fin p × Fin p) (vertices : Finset (Fin n)) :
    Finset (Fin p × Fin n) :=
  ({pair.1,pair.2} : Finset (Fin p)).product vertices

/-- The product of two row labels and two vertex labels. -/
def commonVertexPairRectangle {n p : ℕ} (i j : Fin p) (x y : Fin n) : Finset (Fin p × Fin n) :=
  ({i,j} : Finset (Fin p)).product {x,y}

/-- The incidence rectangles of all pairs counted by `commonVertexPairCount`. -/
def commonVertexPairRectangles {n p : ℕ} (paths : Fin p → List (Fin n)) :
    Finset (Finset (Fin p × Fin n)) :=
  (increasingRowPairs p).biUnion fun pair =>
    ((commonRowPoints paths pair).powersetCard 2).image (commonPairIncidences pair)

theorem commonVertexPairRectangles_card_le {n p : ℕ} (paths : Fin p → List (Fin n)) :
    (commonVertexPairRectangles paths).card ≤ commonVertexPairCount paths := by
  unfold commonVertexPairRectangles
  refine card_biUnion_le.trans (sum_le_sum fun pair _ => ?_)
  rw [← card_powersetCard]
  exact card_image_le

theorem commonVertexPairRectangles_support {n p : ℕ} (paths : Fin p → List (Fin n)) :
    ∀ edge ∈ commonVertexPairRectangles paths, edge ⊆ pieceIncidences paths univ := by
  intro edge on cell atEdge
  obtain ⟨pair,_,placement⟩ := mem_biUnion.mp on
  obtain ⟨points,pointsOn,rfl⟩ := mem_image.mp placement
  obtain ⟨row,col⟩ := mem_product.mp atEdge
  have entry := mem_inter.mp ((mem_powersetCard.mp pointsOn).1 col)
  rcases mem_insert.mp row with first | last
  · exact mem_pieceIncidences.mpr ⟨mem_univ _,first.symm ▸ List.mem_toFinset.mp entry.1⟩
  · have last := mem_singleton.mp last
    exact mem_pieceIncidences.mpr ⟨mem_univ _,last.symm ▸ List.mem_toFinset.mp entry.2⟩

theorem commonVertexPairRectangle_mem {n p : ℕ} {paths : Fin p → List (Fin n)}
    {i j : Fin p} {x y : Fin n} (rows : i ≠ j) (cols : x ≠ y)
    (xi : x ∈ paths i) (yi : y ∈ paths i) (xj : x ∈ paths j) (yj : y ∈ paths j) :
    commonVertexPairRectangle i j x y ∈ commonVertexPairRectangles paths := by
  have inOrder {a b : Fin p} (ordered : a < b)
      (xa : x ∈ paths a) (ya : y ∈ paths a) (xb : x ∈ paths b) (yb : y ∈ paths b) :
      commonVertexPairRectangle a b x y ∈ commonVertexPairRectangles paths := by
    have among : ({x,y} : Finset (Fin n)) ⊆ (paths a).toFinset ∩ (paths b).toFinset := by
      intro v on
      rcases mem_insert.mp on with rfl | last
      · exact mem_inter.mpr ⟨List.mem_toFinset.mpr xa,List.mem_toFinset.mpr xb⟩
      · obtain rfl := mem_singleton.mp last
        exact mem_inter.mpr ⟨List.mem_toFinset.mpr ya,List.mem_toFinset.mpr yb⟩
    apply mem_biUnion.mpr
    refine ⟨(a,b),mem_filter.mpr ⟨mem_univ _,ordered⟩,?_⟩
    exact mem_image.mpr ⟨{x,y},mem_powersetCard.mpr ⟨among,card_pair cols⟩,rfl⟩
  rcases lt_or_gt_of_ne rows with earlier | later
  · exact inOrder earlier xi yi xj yj
  · have same : commonVertexPairRectangle j i x y = commonVertexPairRectangle i j x y := by
      unfold commonVertexPairRectangle
      rw [pair_comm]
    rw [← same]
    exact inOrder later xj yj xi yi

private theorem common_vertex_pairs_unique_sublists_by_hitting_bound {n p loss weight pointWeight : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hit : ∀ (ground : Finset (Fin p × Fin n)) (family : Finset (Finset (Fin p × Fin n))),
      (∀ edge ∈ family, edge ⊆ ground) → (∀ edge ∈ family, edge.card = 4) →
      ∃ chosen ⊆ ground, (∀ edge ∈ family, (edge ∩ chosen).Nonempty) ∧
        loss*chosen.card ≤ weight*family.card+pointWeight*ground.card) :
    let M := ∑ i, (paths i).length
    let E := commonVertexPairCount paths
    ∃ kept : Fin p → List (Fin n),
      (∀ i, (kept i).Sublist (paths i)) ∧
      (∀ {i j x y}, i ≠ j → x ∈ kept i → x ∈ kept j → y ∈ kept i → y ∈ kept j → x = y) ∧
      loss*M ≤ loss*(∑ i, (kept i).length)+weight*E+pointWeight*M := by
  classical
  let ground := pieceIncidences paths univ
  let constraints := commonVertexPairRectangles paths
  have within : ∀ edge ∈ constraints, edge ⊆ ground := commonVertexPairRectangles_support paths
  have sizes : ∀ edge ∈ constraints, edge.card = 4 := by
    intro edge edgeIn
    obtain ⟨pair,present,placement⟩ := mem_biUnion.mp edgeIn
    obtain ⟨vertices,vertexPair,rfl⟩ := mem_image.mp placement
    have ordered := (mem_filter.mp present).2
    change (({pair.1,pair.2} : Finset (Fin p)) ×ˢ vertices).card = 4
    rw [card_product,(mem_powersetCard.mp vertexPair).2,card_pair ordered.ne]
  have constraintCount : constraints.card ≤ commonVertexPairCount paths := commonVertexPairRectangles_card_le paths
  obtain ⟨removed,support,cover,paid⟩ := hit ground constraints within sizes
  let kept := erasePieceIncidences paths removed
  have sub (i : Fin p) : (kept i).Sublist (paths i) := erasePieceIncidences_sublist paths removed i
  have mass := erasePieceIncidences_mass_add_loss simple univ removed
  rw [inter_eq_right.mpr support] at mass
  have groundCard : ground.card = ∑ i, (paths i).length := pieceIncidences_card simple univ
  refine ⟨kept,sub,?_,?_⟩
  · intro i j x y different xi xj yi yj
    by_contra apart
    have edgeOn : commonVertexPairRectangle i j x y ∈ constraints :=
      commonVertexPairRectangle_mem different apart ((sub i).subset xi) ((sub i).subset yi)
        ((sub j).subset xj) ((sub j).subset yj)
    obtain ⟨⟨row,vertex⟩,includes⟩ := cover _ edgeOn
    have deleted := (mem_inter.mp includes).2
    obtain ⟨rowCases,vertexCases⟩ := mem_product.mp (mem_inter.mp includes).1
    simp only [mem_insert,mem_singleton] at rowCases vertexCases
    rcases rowCases with rfl | rfl <;> rcases vertexCases with rfl | rfl
    · exact (mem_erasePieceIncidences.mp xi).2 deleted
    · exact (mem_erasePieceIncidences.mp yi).2 deleted
    · exact (mem_erasePieceIncidences.mp xj).2 deleted
    · exact (mem_erasePieceIncidences.mp yj).2 deleted
  · change (∑ i, (kept i).length)+removed.card = ∑ i, (paths i).length at mass
    have enlarged := paid.trans (Nat.add_le_add_right (Nat.mul_le_mul_left weight constraintCount) (pointWeight*ground.card))
    rw [groundCard] at enlarged
    have split := congrArg (loss * ·) mass
    rw [Nat.mul_add] at split
    rw [← split,Nat.add_assoc]
    exact Nat.add_le_add_left enlarged _

/-- Remove enough incidences to leave at most one vertex in each pairwise
intersection. With starting mass M and common vertex pair count E, the
remaining mass K satisfies 6M ≤ 7K + 3E. -/
theorem common_vertex_pairs_unique_sublists {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) :
    let M := ∑ i, (paths i).length
    let E := commonVertexPairCount paths
    ∃ kept : Fin p → List (Fin n),
      (∀ i, (kept i).Sublist (paths i)) ∧
      (∀ {i j x y}, i ≠ j → x ∈ kept i → x ∈ kept j → y ∈ kept i → y ∈ kept j → x = y) ∧
      6*M ≤ 7*(∑ i, (kept i).length)+3*E := by
  obtain ⟨kept,sub,unique,mass⟩ := common_vertex_pairs_unique_sublists_by_hitting_bound
    (loss := 7) (weight := 3) (pointWeight := 1)
    paths simple (fun ground family within sizes => by
      simpa only [one_mul] using four_point_hitting_set_card ground family within sizes)
  exact ⟨kept,sub,fun {_ _ _ _} => unique,by omega⟩

/-- The maximum-pairing bound on four incidences gives the alternative
retained-mass inequality 12M ≤ 15K + 4E. -/
theorem common_vertex_pairs_unique_sublists_paired {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) :
    let M := ∑ i, (paths i).length
    let E := commonVertexPairCount paths
    ∃ kept : Fin p → List (Fin n),
      (∀ i, (kept i).Sublist (paths i)) ∧
      (∀ {i j x y}, i ≠ j → x ∈ kept i → x ∈ kept j → y ∈ kept i → y ∈ kept j → x = y) ∧
      12*M ≤ 15*(∑ i, (kept i).length)+4*E := by
  obtain ⟨kept,sub,unique,mass⟩ := common_vertex_pairs_unique_sublists_by_hitting_bound
    (loss := 15) (weight := 4) (pointWeight := 3) paths simple
      (fun ground family within sizes => by
        obtain ⟨chosen,inside,hits,_,paid⟩ := four_point_hitting_set_card_paired ground family within sizes
        exact ⟨chosen,inside,hits,paid⟩)
  exact ⟨kept,sub,fun {_ _ _ _} => unique,by omega⟩

/-- The exact factor-four starting caps at half cutoff five follow
if the common vertex pair count is at most 53/72 of the starting mass. -/
theorem regularization_list_frozen_half_five_of_common_vertex_pair_count {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (few : 72*commonVertexPairCount paths ≤ 53*(∑ i, (paths i).length)) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 5 ∧
      M ≤ 288*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  obtain ⟨kept,sub,unique,retain⟩ := common_vertex_pairs_unique_sublists paths simple
  exact regularization_list_frozen_half_five_of_large_unique_sublists paths kept simple free sub
    (fun {_ _ _ _} => unique) hn hp dense long (by omega)

private theorem literal_frozen_half_five_of_indexed {n p : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length)
    (indexed : let M := ∑ i, (paths i).length
      p ≤ M → ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 5 ∧
      M ≤ 288*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 5 ∧
      M ≤ 288*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,all,retain,upper,caps⟩ :=
      regularization_literal_half_full_all_of_low_mass paths distinct valid free (by decide) hn hp dense low
    exact ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,(all 5).halfFree,by omega,upper,caps⟩
  have long : p ≤ M := calc
    _ = ∑ _ : Fin p, (1:ℕ) := by simp
    _ ≤ _ := sum_le_sum (fun i _ => List.length_pos_iff.mpr (valid i).1)
  obtain ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,retain,upper,caps⟩ :=
    indexed long
  have highMean : 4*p < M := by have width := le_max_right n p; omega
  obtain ⟨oneToOne,nonempty⟩ :=
    frozen_length_distinct_of_large_mean rowsSimple rowsFree (by decide) hp highMean caps
  exact ⟨v,vFit,q,qFit,rows,oneToOne,fun i => ⟨nonempty i,rowsSimple i⟩,rowsFree,retain,upper,caps⟩

/-- The same common vertex pair bound gives a witness with distinct
nonempty rows at the exact starting caps. -/
theorem regularization_literal_frozen_half_five_of_common_vertex_pair_count {n p : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length)
    (few : 72*commonVertexPairCount paths ≤ 53*(∑ i, (paths i).length)) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 5 ∧
      M ≤ 288*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  exact literal_frozen_half_five_of_indexed paths distinct valid free hn hp dense (fun long =>
    regularization_list_frozen_half_five_of_common_vertex_pair_count paths (fun i => (valid i).2)
      free hn hp dense long few)

/-- All four starting caps at half cutoff five follow when the common
vertex pair count is at most 31/32 of the starting mass. -/
theorem regularization_list_frozen_half_five_of_paired_incidence_bound {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (few : 32*commonVertexPairCount paths ≤ 31*(∑ i, (paths i).length)) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 5 ∧
      M ≤ 288*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  obtain ⟨kept,sub,unique,retain⟩ := common_vertex_pairs_unique_sublists_paired paths simple
  exact regularization_list_frozen_half_five_of_large_unique_sublists paths kept simple free sub
    (fun {_ _ _ _} => unique) hn hp dense long (by omega)

/-- The same 31/32 condition gives distinct nonempty output
rows at the original starting caps. -/
theorem regularization_literal_frozen_half_five_of_paired_incidence_bound {n p : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length)
    (few : 32*commonVertexPairCount paths ≤ 31*(∑ i, (paths i).length)) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 5 ∧
      M ≤ 288*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  exact literal_frozen_half_five_of_indexed paths distinct valid free hn hp dense (fun long =>
    regularization_list_frozen_half_five_of_paired_incidence_bound paths (fun i => (valid i).2)
      free hn hp dense long few)

end OnlineReachabilityPreservers
