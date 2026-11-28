import OnlineReachabilityPreservers.FullThreeLiteralFeasibility
import OnlineReachabilityPreservers.HalfLatestRowComparisons

/-! The exact literal row budget through half cutoff three. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

theorem card_filter_pair_le_one_of_missing {A : Type*} [DecidableEq A]
    (s : Finset A) (a b : A) (missing : a ∈ s → b ∉ s) :
    (({a,b} : Finset A).filter (· ∈ s)).card ≤ 1 := by
  by_cases aOn : a ∈ s
  · have bOff := missing aOn
    simp [filter_insert,filter_singleton,aOn,bOff]
  · rw [filter_insert,ite_eq_right aOn]
    exact (card_filter_le _ _).trans (by simp)

/-- Restrict a directed edge set to a set of vertices. -/
def arcsOnVertices {V : Type*} [DecidableEq V] (arcs : Finset (V × V)) (s : Finset V) :
    Finset (V × V) := (s ×ˢ s).filter (· ∈ arcs)

theorem mem_arcsOnVertices {V : Type*} [DecidableEq V]
    {arcs : Finset (V × V)} {s : Finset V} {x y : V} :
    (x,y) ∈ arcsOnVertices arcs s ↔ x ∈ s ∧ y ∈ s ∧ (x,y) ∈ arcs := by
  simp only [arcsOnVertices,mem_filter,mem_product,and_assoc]

theorem arcsOnVertices_univ {V : Type*} [Fintype V] [DecidableEq V] (arcs : Finset (V × V)) :
    arcsOnVertices arcs univ = arcs := by
  ext ⟨x,y⟩
  simp only [mem_arcsOnVertices,mem_univ,true_and]

/-- Edges between one vertex and the two indicated endpoints. -/
def arcsLinkingVertexToPair {V : Type*} [DecidableEq V] (arcs : Finset (V × V)) (x y z : V) :
    Finset (V × V) :=
  ({(x,z),(z,x)} ∪ {(y,z),(z,y)} : Finset (V × V)).filter (· ∈ arcs)

theorem at_most_two_links_to_bidirectional_pair {V : Type*} [DecidableEq V]
    {arcs : Finset (V × V)}
    (apart : ∀ {x y z : V}, (x,y) ∈ arcs → (y,x) ∈ arcs → (x,z) ∈ arcs → (y,z) ∉ arcs)
    {x y : V} (xy : (x,y) ∈ arcs) (yx : (y,x) ∈ arcs) (z : V) :
    (arcsLinkingVertexToPair arcs x y z).card ≤ 2 := by
  rw [arcsLinkingVertexToPair,filter_union]
  by_cases xBoth : (x,z) ∈ arcs ∧ (z,x) ∈ arcs
  · have yz : (y,z) ∉ arcs := apart xy yx xBoth.1
    have zy : (z,y) ∉ arcs := apart xBoth.1 xBoth.2 xy
    have absent : ({(y,z),(z,y)} : Finset (V × V)).filter (· ∈ arcs) = ∅ := by
      ext e
      simp only [mem_filter,mem_insert,mem_singleton,notMem_empty,iff_false]
      rintro ⟨eq | eq,on⟩
      · exact yz (eq ▸ on)
      · exact zy (eq ▸ on)
    rw [absent,union_empty]
    exact (card_filter_le _ _).trans card_le_two
  by_cases yBoth : (y,z) ∈ arcs ∧ (z,y) ∈ arcs
  · have xz : (x,z) ∉ arcs := apart yx xy yBoth.1
    have zx : (z,x) ∉ arcs := apart yBoth.1 yBoth.2 yx
    have absent : ({(x,z),(z,x)} : Finset (V × V)).filter (· ∈ arcs) = ∅ := by
      ext e
      simp only [mem_filter,mem_insert,mem_singleton,notMem_empty,iff_false]
      rintro ⟨eq | eq,on⟩
      · exact xz (eq ▸ on)
      · exact zx (eq ▸ on)
    rw [absent,empty_union]
    exact (card_filter_le _ _).trans card_le_two
  exact (card_union_le ..).trans (Nat.add_le_add
    (card_filter_pair_le_one_of_missing _ _ _ fun a b => xBoth ⟨a,b⟩)
    (card_filter_pair_le_one_of_missing _ _ _ fun a b => yBoth ⟨a,b⟩))

/-- Removing two vertices loses their two internal arcs and the links
to the remaining vertices. -/
theorem arcsOnVertices_card_le_erase_pair {V : Type*} [DecidableEq V]
    (arcs : Finset (V × V)) (loopless : ∀ v, (v,v) ∉ arcs) (s : Finset V) (x y : V) :
    let r := (s.erase x).erase y
    (arcsOnVertices arcs s).card ≤ (arcsOnVertices arcs r).card+2+
      (r.biUnion (arcsLinkingVertexToPair arcs x y)).card := by
  let r := (s.erase x).erase y
  let middle : Finset (V × V) := {(x,y),(y,x)}
  have contained : arcsOnVertices arcs s ⊆
      (arcsOnVertices arcs r ∪ middle) ∪ r.biUnion (arcsLinkingVertexToPair arcs x y) := by
    rintro ⟨u,v⟩ on
    obtain ⟨uOn,vOn,uvArc⟩ := mem_arcsOnVertices.mp on
    have into (a : V) (h : a ∈ s) : a ∈ r ∨ a = x ∨ a = y := by
      by_cases ax : a = x
      · exact Or.inr (Or.inl ax)
      by_cases ay : a = y
      · exact Or.inr (Or.inr ay)
      exact Or.inl (mem_erase.mpr ⟨ay,mem_erase.mpr ⟨ax,h⟩⟩)
    rcases into u uOn with ur | rfl | rfl <;> rcases into v vOn with vr | rfl | rfl
    · exact mem_union_left _ (mem_union_left _ (mem_arcsOnVertices.mpr ⟨ur,vr,uvArc⟩))
    · exact mem_union_right _ (mem_biUnion.mpr ⟨u,ur,by simp [arcsLinkingVertexToPair,uvArc]⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨u,ur,by simp [arcsLinkingVertexToPair,uvArc]⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨v,vr,by simp [arcsLinkingVertexToPair,uvArc]⟩)
    · exact (loopless _ uvArc).elim
    · exact mem_union_left _ (mem_union_right _ (by simp [middle]))
    · exact mem_union_right _ (mem_biUnion.mpr ⟨v,vr,by simp [arcsLinkingVertexToPair,uvArc]⟩)
    · exact mem_union_left _ (mem_union_right _ (by simp [middle]))
    · exact (loopless _ uvArc).elim
  exact (card_le_card contained).trans ((card_union_le ..).trans
    (Nat.add_le_add_right ((card_union_le ..).trans (Nat.add_le_add_left card_le_two _)) _))

theorem arcsOnVertices_card_le_of_no_reciprocal {V : Type*} [DecidableEq V]
    (arcs : Finset (V × V)) (loopless : ∀ v, (v,v) ∉ arcs) (s : Finset V)
    (noPair : ¬ ∃ x y, (x,y) ∈ arcsOnVertices arcs s ∧ (y,x) ∈ arcsOnVertices arcs s) :
    2*(arcsOnVertices arcs s).card ≤ s.card*(s.card-1) := by
  let inside := arcsOnVertices arcs s
  let swapped := inside.map (Equiv.prodComm V V).toEmbedding
  have disjoint : Disjoint inside swapped := by
    apply disjoint_left.mpr
    rintro ⟨x,y⟩ on rev
    obtain ⟨⟨v,u⟩,back,eq⟩ := mem_map.mp rev
    have same : (u,v) = (x,y) := eq
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
    exact noPair ⟨_,_,on,back⟩
  have insideOff : inside ⊆ s.offDiag := by
    rintro ⟨x,y⟩ on
    obtain ⟨xOn,yOn,edge⟩ := mem_arcsOnVertices.mp on
    refine mem_offDiag.mpr ⟨xOn,yOn,?_⟩
    change x ≠ y
    rintro rfl
    exact loopless _ edge
  have stays : inside ∪ swapped ⊆ s.offDiag := by
    rintro ⟨x,y⟩ on
    rcases mem_union.mp on with on | rev
    · exact insideOff on
    · obtain ⟨⟨v,u⟩,back,eq⟩ := mem_map.mp rev
      have same : (u,v) = (x,y) := eq
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
      obtain ⟨a,b,ne⟩ := mem_offDiag.mp (insideOff back)
      exact mem_offDiag.mpr ⟨b,a,ne.symm⟩
  have count := card_le_card stays
  rw [card_union_of_disjoint disjoint,show swapped.card = inside.card from card_map _,
    offDiag_card] at count
  simpa only [inside,Nat.mul_sub_left_distrib,mul_one,two_mul] using count

theorem erase_pair_card_add_two {V : Type*} [DecidableEq V] {s : Finset V} {x y : V}
    (xOn : x ∈ s) (yOn : y ∈ s) (different : x ≠ y) : ((s.erase x).erase y).card+2 = s.card := by
  have first := card_erase_add_one xOn
  have second := card_erase_add_one (mem_erase.mpr ⟨different.symm,yOn⟩)
  omega

/-- In a loopless directed graph where the endpoints of every doubled
edge have disjoint out-neighborhoods, at most half of the ordered pairs
are arcs. Remove both endpoints of a doubled edge and count at most
two incident arcs per other vertex. -/
theorem directed_arcs_card_le_half_square_of_bidirectional_out_disjoint {V : Type*}
    [Fintype V] [DecidableEq V] (arcs : Finset (V × V))
    (loopless : ∀ v, (v,v) ∉ arcs)
    (apart : ∀ {x y z : V}, (x,y) ∈ arcs → (y,x) ∈ arcs → (x,z) ∈ arcs → (y,z) ∉ arcs) :
    2*arcs.card ≤ (Fintype.card V)^2 := by
  have bound (s : Finset V) : 2*(arcsOnVertices arcs s).card ≤ s.card^2 := by
    refine Finset.strongInductionOn (p := fun t => 2*(arcsOnVertices arcs t).card ≤ t.card^2) s ?_
    intro s ih
    by_cases double : ∃ x y, (x,y) ∈ arcsOnVertices arcs s ∧ (y,x) ∈ arcsOnVertices arcs s
    · obtain ⟨x,y,xy,yx⟩ := double
      obtain ⟨xOn,yOn,xyArc⟩ := mem_arcsOnVertices.mp xy
      have yxArc := (mem_arcsOnVertices.mp yx).2.2
      have different : x ≠ y := by rintro rfl; exact loopless _ xyArc
      let r := (s.erase x).erase y
      have count : r.card+2 = s.card := erase_pair_card_add_two xOn yOn different
      have sub : r ⊂ s := Finset.ssubset_iff_subset_ne.mpr
        ⟨(erase_subset _ _).trans (erase_subset _ _),fun same => by rw [same] at count; omega⟩
      have links : (r.biUnion (arcsLinkingVertexToPair arcs x y)).card ≤ r.card*2 :=
        card_biUnion_le_card_mul r _ 2
          (fun z _ => at_most_two_links_to_bidirectional_pair @apart xyArc yxArc z)
      have remove := arcsOnVertices_card_le_erase_pair arcs loopless s x y
      change (arcsOnVertices arcs s).card ≤ (arcsOnVertices arcs r).card+2+
        (r.biUnion (arcsLinkingVertexToPair arcs x y)).card at remove
      have prior := ih r sub
      have computed : s.card^2 = r.card^2+4*r.card+4 := by rw [← count]; ring
      omega
    · exact (arcsOnVertices_card_le_of_no_reciprocal arcs loopless s double).trans
        (by rw [pow_two]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  simpa only [arcsOnVertices_univ,card_univ] using bound (univ : Finset V)

/-- Keep only the directed comparisons at consecutive positions. -/
def rowAdjacentComparisons {I V : Type*} [Fintype V] [DecidableEq V]
    (rows : I → List V) (i : I) : Finset (V × V) :=
  (rowDirectedComparisons rows i).filter fun e => (rows i).idxOf e.2 = (rows i).idxOf e.1+1

theorem mem_rowAdjacentComparisons {I V : Type*} [Fintype V] [DecidableEq V]
    {rows : I → List V} {i : I} {x y : V} :
    (x,y) ∈ rowAdjacentComparisons rows i ↔ Before rows i x y ∧
      (rows i).idxOf y = (rows i).idxOf x+1 := by
  rw [rowAdjacentComparisons,mem_filter,mem_rowDirectedComparisons]

theorem rowAdjacentComparisons_card {I V : Type*} [Fintype V] [DecidableEq V]
    {rows : I → List V} {i : I} (simple : (rows i).Nodup) :
    (rowAdjacentComparisons rows i).card = (rows i).length-1 := by
  let row := rows i
  let slot := Fin (row.length-1)
  let pair (j : slot) : V × V :=
    (row[j.val]'(by have := j.isLt; omega),row[j.val+1]'(by have := j.isLt; omega))
  have index (j : slot) : row.idxOf (pair j).1 = j.val ∧ row.idxOf (pair j).2 = j.val+1 := by
    dsimp only [pair]
    rw [simple.idxOf_getElem,simple.idxOf_getElem]
    simp
  have pairInjective : Function.Injective pair := by
    intro j k eq
    exact Fin.ext ((index j).1.symm.trans ((congrArg (fun e : V × V => row.idxOf e.1) eq).trans (index k).1))
  have same : rowAdjacentComparisons rows i = univ.map ⟨pair,pairInjective⟩ := by
    ext e
    rcases e with ⟨x,y⟩
    simp only [mem_rowAdjacentComparisons,mem_map,Function.Embedding.coeFn_mk,mem_univ,true_and]
    constructor
    · rintro ⟨step,neighbor⟩
      have left := List.idxOf_lt_length_of_mem step.1
      have right := List.idxOf_lt_length_of_mem step.2.1
      let j : slot := ⟨row.idxOf x,by change (rows i).idxOf x < (rows i).length-1; omega⟩
      refine ⟨j,Prod.ext ?_ ?_⟩
      · exact List.getElem_idxOf left
      · apply (List.idxOf_inj (List.getElem_mem _)).mp
        exact (index j).2.trans neighbor.symm
    · rintro ⟨j,eq⟩
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (show ((pair j).1,(pair j).2) = (x,y) from eq)
      have adjacent := (index j).2.trans (congrArg (·+1) (index j).1.symm)
      refine ⟨⟨List.getElem_mem _,List.getElem_mem _,?_⟩,adjacent⟩
      change row.idxOf (pair j).1 < row.idxOf (pair j).2
      omega
  rw [same,card_map,card_univ,Fintype.card_fin]

/-- At the half-three cutoff, a transitive triangle of adjacent steps
requires the shortcut to arrive before the final step of the detour. -/
theorem halfThree_adjacent_triangle_order {I V : Type*} [LinearOrder I] [Fintype V] [DecidableEq V]
    {rows : I → List V} {k : ℕ} (free : HalfBridgeFree (Before rows) k) (three : 3 ≤ k)
    {a b r : I} {x y z : V} (first : (x,y) ∈ rowAdjacentComparisons rows a)
    (last : (y,z) ∈ rowAdjacentComparisons rows b) (shortcut : (x,z) ∈ rowAdjacentComparisons rows r) :
    r < b := by
  obtain ⟨firstStep,firstAdj⟩ := mem_rowAdjacentComparisons.mp first
  obtain ⟨lastStep,lastAdj⟩ := mem_rowAdjacentComparisons.mp last
  obtain ⟨riverStep,riverAdj⟩ := mem_rowAdjacentComparisons.mp shortcut
  have ra : r ≠ a := by
    rintro rfl
    have equal := (List.idxOf_inj riverStep.2.1).mp (riverAdj.trans firstAdj.symm)
    exact listBefore_ne lastStep equal.symm
  have rb : r ≠ b := by
    rintro rfl
    have equal := (List.idxOf_inj riverStep.1).mp
      (Nat.add_right_cancel (riverAdj.symm.trans lastAdj))
    exact listBefore_ne firstStep equal
  have ab : a ≠ b := by
    rintro rfl
    apply no_parallel_list_steps free (by omega) ra.symm _ riverStep
    exact ⟨firstStep.1,lastStep.2.1,firstStep.2.2.trans lastStep.2.2⟩
  have excluded : ¬ b < r := free three (threeListBridge ab ra rb firstStep lastStep riverStep)
  exact lt_of_le_of_ne (le_of_not_gt excluded) rb

theorem mem_familyAdjacentComparisons {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    {rows : I → List V} {x y : V} :
    (x,y) ∈ univ.biUnion (rowAdjacentComparisons rows) ↔ ∃ i, (x,y) ∈ rowAdjacentComparisons rows i := by
  simp

/-- Reciprocal adjacent comparisons prevent a common out-neighbor,
since two triangles would force opposite orders into that target. -/
theorem halfThree_adjacent_no_common_out {I V : Type*}
    [LinearOrder I] [Fintype I] [Fintype V] [DecidableEq V]
    {rows : I → List V} {k : ℕ} (free : HalfBridgeFree (Before rows) k) (three : 3 ≤ k)
    {x y z : V} (xy : (x,y) ∈ univ.biUnion (rowAdjacentComparisons rows))
    (yx : (y,x) ∈ univ.biUnion (rowAdjacentComparisons rows))
    (xz : (x,z) ∈ univ.biUnion (rowAdjacentComparisons rows)) :
    (y,z) ∉ univ.biUnion (rowAdjacentComparisons rows) := by
  intro yz
  obtain ⟨_,xy⟩ := mem_familyAdjacentComparisons.mp xy
  obtain ⟨_,yx⟩ := mem_familyAdjacentComparisons.mp yx
  obtain ⟨_,xz⟩ := mem_familyAdjacentComparisons.mp xz
  obtain ⟨_,yz⟩ := mem_familyAdjacentComparisons.mp yz
  exact (halfThree_adjacent_triangle_order free three xy yz xz).asymm
    (halfThree_adjacent_triangle_order free three yx xz yz)

/-- Shortcuts to the same terminal give opposing arrival constraints
if the two starting vertices also have both adjacent directions. -/
theorem halfThree_adjacent_comparisons_card_le_half_square {I V : Type*}
    [LinearOrder I] [Fintype I] [Fintype V] [DecidableEq V]
    {rows : I → List V} {k : ℕ} (free : HalfBridgeFree (Before rows) k) (three : 3 ≤ k) :
    2*(univ.biUnion (rowAdjacentComparisons rows)).card ≤ (Fintype.card V)^2 := by
  apply directed_arcs_card_le_half_square_of_bidirectional_out_disjoint (univ.biUnion (rowAdjacentComparisons rows))
  · intro v on
    obtain ⟨_,on⟩ := mem_familyAdjacentComparisons.mp on
    exact listBefore_ne (mem_rowAdjacentComparisons.mp on).1 rfl
  · intro x y z
    exact halfThree_adjacent_no_common_out free three

/-- Adjacent steps from different rows have distinct directed pairs. -/
theorem familyAdjacentComparisons_card {I V : Type*}
    [LinearOrder I] [Fintype I] [Fintype V] [DecidableEq V]
    {rows : I → List V} {k : ℕ} (simple : ∀ i, (rows i).Nodup)
    (free : HalfBridgeFree (Before rows) k) (two : 2 ≤ k) :
    (univ.biUnion (rowAdjacentComparisons rows)).card = ∑ i, ((rows i).length-1) := by
  have unique : ((univ : Finset I) : Set I).PairwiseDisjoint (rowAdjacentComparisons rows) := by
    intro i _ j _ different
    refine disjoint_left.mpr ?_
    rintro ⟨x,y⟩ one other
    exact no_parallel_list_steps free two different (mem_rowAdjacentComparisons.mp one).1
      (mem_rowAdjacentComparisons.mp other).1
  rw [card_biUnion unique]
  exact sum_congr rfl fun i _ => rowAdjacentComparisons_card (simple i)

/-- The total number of consecutive steps counts each occupied ordered
pair once. Half-three exclusion bounds that total by half the square of
the vertex budget, even with empty rows. -/
theorem halfThree_row_gaps_le_half_square {I V : Type*}
    [LinearOrder I] [Fintype I] [Fintype V] [DecidableEq V]
    {rows : I → List V} {k : ℕ} (simple : ∀ i, (rows i).Nodup)
    (free : HalfBridgeFree (Before rows) k) (three : 3 ≤ k) :
    2*(∑ i, ((rows i).length-1)) ≤ (Fintype.card V)^2 := by
  rw [← familyAdjacentComparisons_card simple free (by omega)]
  exact halfThree_adjacent_comparisons_card_le_half_square free three

theorem rowMass_eq_gaps_add_count {I V : Type*} [Fintype I] {rows : I → List V}
    (nonempty : ∀ i, rows i ≠ []) : (∑ i, (rows i).length) = (∑ i, ((rows i).length-1))+Fintype.card I := calc
    _ = ∑ i, (((rows i).length-1)+1) :=
      sum_congr rfl fun i _ => (Nat.sub_add_cancel (List.length_pos_iff.mpr (nonempty i))).symm
    _ = _ := by rw [sum_add_distrib]; simp

/-- Relative to the number of nonempty rows, the incidence mass exceeds
that count by at most the balanced bidirectional pair capacity. -/
theorem halfThree_mass_le_paths_add_balanced_pairs {n p k : ℕ} {rows : Fin p → List (Fin n)}
    (valid : ∀ i, rows i ≠ [] ∧ (rows i).Nodup)
    (free : HalfBridgeFree (Before rows) k) (three : 3 ≤ k) :
    (∑ i, (rows i).length) ≤ p+2*((n/2)*(n-n/2)) := by
  have raw := halfThree_row_gaps_le_half_square (fun i => (valid i).2) free three
  rw [Fintype.card_fin] at raw
  have bound := balancedLayer_product raw
  have mass := rowMass_eq_gaps_add_count (fun i => (valid i).1)
  rw [Fintype.card_fin] at mass
  omega

/-- In a distinct nonempty family, each singleton uses a different
vertex and each longer row supplies a consecutive step. -/
theorem literal_path_count_le_vertices_add_gaps {n p : ℕ} {rows : Fin p → List (Fin n)}
    (distinct : Function.Injective rows) (nonempty : ∀ i, rows i ≠ []) :
    p ≤ n+∑ i, ((rows i).length-1) := by
  let singles := (univ : Finset (Fin p)).filter fun i => (rows i).length = 1
  let label (i : singles) := (rows i.val)[0]'(List.length_pos_iff.mpr (nonempty i.val))
  have single (i : singles) : rows i.val = [label i] := by
    obtain ⟨v,asList⟩ := List.length_eq_one_iff.mp (mem_filter.mp i.property).2
    have vertex : label i = v := by unfold label; rw [List.getElem_of_eq asList]; rfl
    rwa [vertex]
  have labelInjective : Function.Injective label := by
    intro i j same
    apply Subtype.ext
    exact distinct ((single i).trans ((congrArg (fun v => [v]) same).trans (single j).symm))
  have singleBound : singles.card ≤ n := by
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective label labelInjective
  have counted : (∑ i : Fin p, if i ∈ singles then (1:ℕ) else 0) = singles.card := by
    rw [← sum_filter,filter_mem_eq_inter,univ_inter]
    simp
  have pays (i : Fin p) : 1 ≤ (if i ∈ singles then 1 else 0)+((rows i).length-1) := by
    by_cases singleton : i ∈ singles
    · simp [singleton]
    · have positive := List.length_pos_iff.mpr (nonempty i)
      have notOne : (rows i).length ≠ 1 := by simpa [singles] using singleton
      simp only [ite_eq_right singleton,zero_add]
      omega
  have count : p ≤ singles.card+∑ i, ((rows i).length-1) := by
    simpa only [sum_add_distrib,counted,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,mul_one] using
      (sum_le_sum (s := (univ : Finset (Fin p))) (fun i _ => pays i))
  omega

/-- Distinct literal half-three rows fit the balanced bidirectional
pair capacity plus at most one singleton per vertex. -/
theorem literal_half_path_count_le_balanced_bipartite {n p k : ℕ} {rows : Fin p → List (Fin n)}
    (distinct : Function.Injective rows) (valid : ∀ i, rows i ≠ [] ∧ (rows i).Nodup)
    (free : HalfBridgeFree (Before rows) k) (three : 3 ≤ k) :
    p ≤ n+2*((n/2)*(n-n/2)) := by
  have raw := halfThree_row_gaps_le_half_square (fun i => (valid i).2) free three
  rw [Fintype.card_fin] at raw
  exact (literal_path_count_le_vertices_add_gaps distinct (fun i => (valid i).1)).trans
    (Nat.add_le_add_left (balancedLayer_product raw) n)

/-- The exact literal half-three and full-three feasibility regions
coincide. The balanced bidirectional construction gives the converse. -/
theorem literal_half_three_feasible_iff {n p : ℕ} :
    (∃ rows : Fin p → List (Fin n), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 3) ↔
    p ≤ n+2*((n/2)*(n-n/2)) := by
  constructor
  · rintro ⟨rows,distinct,valid,free⟩
    exact literal_half_path_count_le_balanced_bipartite distinct valid free le_rfl
  · intro fits
    obtain ⟨rows,distinct,valid,free⟩ := literal_full_three_feasible_iff.mpr fits
    exact ⟨rows,distinct,valid,free.halfFree⟩

end OnlineReachabilityPreservers
