import OnlineReachabilityPreservers.HalfFiveTerminalRank
import OnlineReachabilityPreservers.HalfFiveDegreeRepair
import Mathlib.Data.Finset.Sort

/-! Pack the incidences constrained by projected half-five patterns into the first degree block. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

variable {n p : ℕ}

/-- Original rows that participate in a projected collision constraint
at this vertex. -/
noncomputable def halfFiveCollisionProtectedRows (paths : Fin p → List (Fin n)) (v : Fin n) : Finset (Fin p) := by
  classical
  exact (occurrences (fun i => (paths i).toFinset) v).filter fun i =>
    (∃ j, Edge (halfFiveCollisionRankGraph paths v) i j) ∨ ∃ j, Edge (halfFiveCollisionRankGraph paths v) j i

private theorem collisionProtected_subset (paths : Fin p → List (Fin n)) (v : Fin n) :
    halfFiveCollisionProtectedRows paths v ⊆ occurrences (fun i => (paths i).toFinset) v :=
  filter_subset _ _

private theorem collisionProtected_edge {paths : Fin p → List (Fin n)} {v : Fin n} {a b : Fin p}
    (edge : Edge (halfFiveCollisionRankGraph paths v) a b) :
    a ∈ halfFiveCollisionProtectedRows paths v ∧ b ∈ halfFiveCollisionProtectedRows paths v := by
  classical
  have seen : v ∈ paths a ∧ v ∈ paths b := by
    obtain ⟨h,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := halfFiveCollisionRankGraph_edge.mp edge
    · exact ⟨(congrArg (fun x => x ∈ paths h.triangle.river) h.terminal).mp h.triangle.riverStep.2.1,
        (congrArg (fun x => x ∈ paths (h.triangle.arc 1)) h.terminal).mp (h.triangle.arcStep 1).2.1⟩
    · exact ⟨h.outStep.1,h.inStep.2.1⟩
  exact ⟨mem_filter.mpr ⟨mem_occurrences.mpr (List.mem_toFinset.mpr seen.1),Or.inl ⟨b,edge⟩⟩,
    mem_filter.mpr ⟨mem_occurrences.mpr (List.mem_toFinset.mpr seen.2),Or.inr ⟨a,edge⟩⟩⟩

private def protectedFirstPackingOrder {R : Type*} [LinearOrder R] (all forced : Finset R) : List R :=
  forced.sort (· ≤ ·) ++ (all \ forced).sort (· ≤ ·)

private theorem protectedFirstPackingOrder_mem {R : Type*} [LinearOrder R] {all forced : Finset R} {x : R}
    (sub : forced ⊆ all) : x ∈ protectedFirstPackingOrder all forced ↔ x ∈ all := by
  unfold protectedFirstPackingOrder
  simp only [List.mem_append,mem_sort,mem_sdiff]
  constructor
  · exact fun h => h.elim (fun on => sub on) And.left
  · intro on
    by_cases selected : x ∈ forced
    · exact Or.inl selected
    · exact Or.inr ⟨on,selected⟩

private theorem protectedFirstPackingOrder_length {R : Type*} [LinearOrder R] {all forced : Finset R}
    (sub : forced ⊆ all) : (protectedFirstPackingOrder all forced).length = all.card := by
  unfold protectedFirstPackingOrder
  simp only [List.length_append,length_sort]
  rw [Nat.add_comm]
  exact card_sdiff_add_card_eq_card sub

private theorem protectedFirstPackingOrder_forced_position {R : Type*} [LinearOrder R]
    {all forced : Finset R} {x : R} (selected : x ∈ forced) :
    (protectedFirstPackingOrder all forced).idxOf x < forced.card := by
  let first := forced.sort (· ≤ ·)
  have present : x ∈ first := (mem_sort _).mpr selected
  unfold protectedFirstPackingOrder
  rw [List.idxOf_append_of_mem present,← length_sort (r := (· ≤ ·))]
  exact List.idxOf_lt_length_of_mem present

private theorem packingOrder_block_card {R : Type*} [DecidableEq R] (order : List R) {S : Finset R}
    {w : ℕ} (positive : 0 < w) (q : ℕ)
    (positions : ∀ x ∈ S, x ∈ order ∧ order.idxOf x / w = q) : S.card ≤ w := by
  let idx (x : R) := order.idxOf x
  calc
    _ ≤ (range w).card := by
      apply card_le_card_of_injOn (fun x => idx x % w)
      · intro x _
        exact mem_range.mpr (Nat.mod_lt _ positive)
      · intro x onX y onY equal
        obtain ⟨presentX,blockX⟩ := positions x onX
        obtain ⟨_,blockY⟩ := positions y onY
        change idx x / w = q at blockX
        change idx y / w = q at blockY
        change idx x % w = idx y % w at equal
        have divX := Nat.mod_add_div (idx x) w
        have divY := Nat.mod_add_div (idx y) w
        rw [blockX] at divX
        rw [blockY] at divY
        exact (List.idxOf_inj presentX).mp (show idx x = idx y by omega)
    _ = _ := card_range _

private noncomputable def collisionPackingOrder (paths : Fin p → List (Fin n)) (v : Fin n) : List (Fin p) :=
  protectedFirstPackingOrder (occurrences (fun i => (paths i).toFinset) v) (halfFiveCollisionProtectedRows paths v)

private theorem collisionPackingOrder_mem {paths : Fin p → List (Fin n)} {v : Fin n} {i : Fin p} :
    i ∈ collisionPackingOrder paths v ↔ i ∈ occurrences (fun j => (paths j).toFinset) v :=
  protectedFirstPackingOrder_mem (collisionProtected_subset paths v)

private theorem collisionPackingOrder_length (paths : Fin p → List (Fin n)) (v : Fin n) :
    (collisionPackingOrder paths v).length = (occurrences (fun j => (paths j).toFinset) v).card :=
  protectedFirstPackingOrder_length (collisionProtected_subset paths v)

private theorem collisionPackingOrder_forced_position {paths : Fin p → List (Fin n)} {v : Fin n} {i : Fin p}
    (forced : i ∈ halfFiveCollisionProtectedRows paths v) :
    (collisionPackingOrder paths v).idxOf i < (halfFiveCollisionProtectedRows paths v).card :=
  protectedFirstPackingOrder_forced_position forced

private noncomputable def collisionPackedCopy (paths : Fin p → List (Fin n)) (D : ℕ) (i : Fin p)
    (v : {v // v ∈ paths i}) : ListVertexBlockIndex paths D :=
  ⟨v.val,⟨(collisionPackingOrder paths v.val).idxOf i / D,by
    have member : i ∈ collisionPackingOrder paths v.val := collisionPackingOrder_mem.mpr
      (mem_occurrences.mpr (List.mem_toFinset.mpr v.property))
    have bounded := List.idxOf_lt_length_of_mem member
    rw [collisionPackingOrder_length] at bounded
    exact Nat.lt_succ_of_le (Nat.div_le_div_right bounded.le)⟩⟩

/-- Use the usual degree-block alphabet and put the constrained
occurrences first in each vertex's packing order. -/
noncomputable def halfFiveCollisionPackedPaths (paths : Fin p → List (Fin n)) (D : ℕ)
    (i : Fin p) : List (ListVertexBlockIndex paths D) :=
  (paths i).attach.map (collisionPackedCopy paths D i)

theorem halfFiveCollisionPackedPaths_project (paths : Fin p → List (Fin n)) (D : ℕ) (i : Fin p) :
    ((halfFiveCollisionPackedPaths paths D i).map fun v => v.fst) = paths i := by
  unfold halfFiveCollisionPackedPaths
  rw [List.map_map]
  exact List.attach_map_subtype_val _

private theorem collisionPackedPaths_mem {paths : Fin p → List (Fin n)} {D : ℕ} {i : Fin p}
    {v : ListVertexBlockIndex paths D} (on : v ∈ halfFiveCollisionPackedPaths paths D i) :
    v.fst ∈ paths i ∧ v.snd.val = (collisionPackingOrder paths v.fst).idxOf i / D := by
  obtain ⟨old,_,rfl⟩ := List.mem_map.mp on
  exact ⟨old.property,rfl⟩

/-- Each occupied degree block uses at most its prescribed width. -/
theorem halfFiveCollisionPackedPaths_degree {paths : Fin p → List (Fin n)} {D : ℕ} (positive : 0 < D)
    (v : ListVertexBlockIndex paths D) :
    (occurrences (fun i => (halfFiveCollisionPackedPaths paths D i).toFinset) v).card ≤ D := by
  let order := collisionPackingOrder paths v.fst
  apply packingOrder_block_card order positive v.snd.val
  intro i on
  have present : v ∈ halfFiveCollisionPackedPaths paths D i := List.mem_toFinset.mp
    ((mem_occurrences (marks := fun j => (halfFiveCollisionPackedPaths paths D j).toFinset)).mp on)
  have copied := collisionPackedPaths_mem present
  exact ⟨collisionPackingOrder_mem.mpr (mem_occurrences.mpr (List.mem_toFinset.mpr copied.1)),copied.2.symm⟩

/-- If the constrained rows at each vertex fit one degree block, the
packing keeps every original comparison and preserves half-five exclusion. -/
theorem halfFiveCollisionPackedPaths_halfFree {paths : Fin p → List (Fin n)} {D : ℕ}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5)
    (room : ∀ v, (halfFiveCollisionProtectedRows paths v).card ≤ D) :
    HalfBridgeFree (Before (halfFiveCollisionPackedPaths paths D)) 5 := by
  let W := ListVertexBlockIndex paths D
  let project (x : W) := x.fst
  let rank (x : W) := x.snd.val
  let assigned (i : Fin p) (v : Fin n) := (collisionPackingOrder paths v).idxOf i / D
  have step {i x y} (found : Before (halfFiveCollisionPackedPaths paths D) i x y) :
      Before paths i (project x) (project y) := by
    have shape (i : Fin p) : ((halfFiveCollisionPackedPaths paths D i).map project) = paths i :=
      halfFiveCollisionPackedPaths_project paths D i
    have old := listBefore_map project ((shape i).symm ▸ simple i) found
    simpa only [SourceAudit.BeforeIn,shape] using old
  refine free.split_list_vertices_five_of_collision_rank_graph project rank assigned
    (fun {_ _} => vertexBlock_eq_of_same_label) (fun on => (collisionPackedPaths_mem on).2) ?_
    (fun {_ _ _} => step)
  intro v a b edge
  obtain ⟨left,right⟩ := collisionProtected_edge edge
  have leftZero : assigned a v = 0 := Nat.div_eq_of_lt ((collisionPackingOrder_forced_position left).trans_le (room v))
  have rightZero : assigned b v = 0 := Nat.div_eq_of_lt ((collisionPackingOrder_forced_position right).trans_le (room v))
  rw [leftZero,rightZero]

/-- At half cutoff five, a path family already within the original length
cap needs only the vertex packing. If the local constraints fit their first
blocks, the frozen witness retains at least a quarter of the input mass. -/
theorem regularization_list_frozen_half_five_of_small_collision_support {paths : Fin p → List (Fin n)}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (room : let M := ∑ i, (paths i).length
      ∀ v, (halfFiveCollisionProtectedRows paths v).card ≤ 4*M/n)
    (short : let M := ∑ i, (paths i).length
      ∀ i, (paths i).length ≤ 4*M/p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let rows := halfFiveCollisionPackedPaths paths D
  obtain ⟨positive,extra,_⟩ := four_average_width hn dense
  change 0 < D at positive
  change 3*(M/D) ≤ n at extra
  have vSize := (regularization_list_counts paths simple positive (L := 1) (by decide)).1
  simp only [Fintype.card_fin] at vSize
  change Fintype.card (ListVertexBlockIndex paths D) ≤ n+M/D at vSize
  have vCap : 3*Fintype.card (ListVertexBlockIndex paths D) ≤ 4*n := by omega
  have length (i : Fin p) : (rows i).length = (paths i).length := by simp [rows,halfFiveCollisionPackedPaths]
  have mass : (∑ i, (rows i).length) = M := sum_congr rfl (fun i _ => length i)
  have rowSimple (i : Fin p) : (rows i).Nodup :=
    List.Nodup.of_map (fun v => v.fst) ((halfFiveCollisionPackedPaths_project paths D i).symm ▸ simple i)
  exact regularization_list_frozen_after_caps_with_ratios (half := true) (k := 5) (retention := 4)
    (vNum := 3) (vDen := 4) (pNum := 1) (pDen := 1) rows rowSimple
    (halfFiveCollisionPackedPaths_halfFree simple free room) hn hp dense long
    (by decide) (by decide) (by decide) (by decide) vCap (by simp)
    (fun i => (length i).trans_le (short i)) (halfFiveCollisionPackedPaths_degree positive) mass (by decide)

section PathPacking

variable {I V : Type*} [LinearOrder I] [Fintype I] [LinearOrder V]

/-- Protect both endpoints of every comparison reversed on another row. -/
noncomputable def halfFiveReverseProtectedVertices (paths : I → List V) (i : I) : Finset V := by
  classical
  exact (paths i).toFinset.filter fun x => ∃ j, i ≠ j ∧ ∃ y,
    (Before paths i x y ∧ Before paths j y x) ∨ (Before paths i y x ∧ Before paths j x y)

private theorem reverseProtected_subset (paths : I → List V) (i : I) :
    halfFiveReverseProtectedVertices paths i ⊆ (paths i).toFinset := by
  classical
  exact filter_subset _ _

private theorem reverseProtected_pair {paths : I → List V} {i j : I} {x y : V}
    (different : i ≠ j) (forward : Before paths i x y) (backward : Before paths j y x) :
    x ∈ halfFiveReverseProtectedVertices paths i ∧ y ∈ halfFiveReverseProtectedVertices paths i := by
  classical
  exact ⟨mem_filter.mpr ⟨List.mem_toFinset.mpr forward.1,j,different,y,Or.inl ⟨forward,backward⟩⟩,
    mem_filter.mpr ⟨List.mem_toFinset.mpr forward.2.1,j,different,x,Or.inr ⟨forward,backward⟩⟩⟩

private noncomputable def reversePackingOrder (paths : I → List V) (i : I) : List V :=
  protectedFirstPackingOrder (paths i).toFinset (halfFiveReverseProtectedVertices paths i)

private noncomputable def reversePackedRow (paths : I → List V) (w : ℕ) (i : I) (q : ℕ) : List V :=
  (paths i).filter fun v => decide ((reversePackingOrder paths i).idxOf v / w = q)

/-- Assign width blocks with the protected endpoints first, and retain
the original comparison order within each piece. -/
noncomputable def halfFiveReversePackedPaths (paths : I → List V) (w : ℕ)
    (i : ListBlockIndex paths w) : List V :=
  reversePackedRow paths w i.fst i.snd.val

private theorem reversePackedPaths_sublist (paths : I → List V) (w : ℕ) (i : ListBlockIndex paths w) :
    (halfFiveReversePackedPaths paths w i).Sublist (paths i.fst) := List.filter_sublist

private theorem mem_reversePackedPaths {paths : I → List V} {w : ℕ} {i : ListBlockIndex paths w} {v : V} :
    v ∈ halfFiveReversePackedPaths paths w i ↔ v ∈ paths i.fst ∧ (reversePackingOrder paths i.fst).idxOf v / w = i.snd.val := by
  simp [halfFiveReversePackedPaths,reversePackedRow]

omit [LinearOrder I] [Fintype I] in
private theorem reversePackedPaths_same_of_label {paths : I → List V} {w : ℕ} {i j : ListBlockIndex paths w}
    (parent : i.fst = j.fst) (block : i.snd.val = j.snd.val) : i = j := by
  rcases i with ⟨i,a⟩
  rcases j with ⟨j,b⟩
  change i = j at parent
  subst j
  change a.val = b.val at block
  have equal : a = b := Fin.ext block
  subst b
  rfl

private theorem reversePackedPaths_disjoint {paths : I → List V} {w : ℕ} {i j : ListBlockIndex paths w} {v : V}
    (different : i ≠ j) (parent : i.fst = j.fst) (left : v ∈ halfFiveReversePackedPaths paths w i)
    (right : v ∈ halfFiveReversePackedPaths paths w j) : False := by
  have fromI := (mem_reversePackedPaths.mp left).2
  have fromJ := (mem_reversePackedPaths.mp right).2
  have compares := congrArg (fun a => (reversePackingOrder paths a).idxOf v / w) parent
  exact different (reversePackedPaths_same_of_label parent (fromI.symm.trans (compares.trans fromJ)))

/-- Packing the protected endpoints together preserves half-five through
these possibly noncontiguous path splits. -/
theorem halfFiveReversePackedPaths_halfFree {paths : I → List V} {w : ℕ}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5)
    (room : ∀ i, (halfFiveReverseProtectedVertices paths i).card ≤ w) :
    HalfBridgeFree (Before (halfFiveReversePackedPaths paths w)) 5 := by
  let pieces := halfFiveReversePackedPaths paths w
  have step {i x y} (on : Before pieces i x y) : Before paths i.fst x y :=
    listBefore_of_sublist (paths := fun a : ListBlockIndex paths w => paths a.fst) (cut := pieces)
      (simple i.fst) (reversePackedPaths_sublist paths w i) on
  have together {i j q : ListBlockIndex paths w} {x y : V} (parent : i.fst = j.fst)
      (apart : i.fst ≠ q.fst) (forward : Before paths i.fst x y) (backward : Before pieces q y x)
      (onI : x ∈ pieces i) (onJ : y ∈ pieces j) : i = j := by
    obtain ⟨xProtected,yProtected⟩ := reverseProtected_pair apart forward (step backward)
    have blockX : (reversePackingOrder paths i.fst).idxOf x / w = 0 :=
      Nat.div_eq_of_lt ((protectedFirstPackingOrder_forced_position xProtected).trans_le (room i.fst))
    have blockY : (reversePackingOrder paths i.fst).idxOf y / w = 0 :=
      Nat.div_eq_of_lt ((protectedFirstPackingOrder_forced_position yProtected).trans_le (room i.fst))
    have atI := (mem_reversePackedPaths.mp onI).2
    have atJ := (mem_reversePackedPaths.mp onJ).2
    have compares := congrArg (fun a => (reversePackingOrder paths a).idxOf y / w) parent
    rw [blockX] at atI
    exact reversePackedPaths_same_of_label parent (atI.symm.trans (blockY.symm.trans (compares.trans atJ)))
  intro d small b earlier
  let old := listBridge_after_opposite_safe_split_through_five Sigma.fst (fun {_ _ _} => step)
    (fun {_ _ _} => reversePackedPaths_disjoint)
    (fun _ {_ _ _ _} diff left right => no_parallel_list_steps free (by decide) diff left right)
    (fun _ {_ _ _ _ _} => together) (by omega) b
  apply free small old
  exact lt_of_le_of_ne (block_parent_mono (fun i => (paths i).toFinset) w earlier.le) (old.river_ne_arc _).symm

/-- Each path piece also respects the block width. -/
theorem halfFiveReversePackedPaths_length {paths : I → List V} {w : ℕ}
    (simple : ∀ i, (paths i).Nodup) (width : 0 < w) (i : ListBlockIndex paths w) :
    (halfFiveReversePackedPaths paths w i).length ≤ w := by
  have pieceSimple := (reversePackedPaths_sublist paths w i).nodup (simple i.fst)
  rw [← List.toFinset_card_of_nodup pieceSimple]
  apply packingOrder_block_card (reversePackingOrder paths i.fst) width i.snd.val
  intro v on
  obtain ⟨original,r⟩ := mem_reversePackedPaths.mp (List.mem_toFinset.mp on)
  exact ⟨(protectedFirstPackingOrder_mem (reverseProtected_subset paths i.fst)).mpr (List.mem_toFinset.mpr original),r⟩

/-- Splitting only partitions the incidences of each row. -/
theorem halfFiveReversePackedPaths_mass (paths : I → List V) (simple : ∀ i, (paths i).Nodup) (w : ℕ) :
    (∑ i, (halfFiveReversePackedPaths paths w i).length) = ∑ i, (paths i).length := by
  change (∑ i : (Σ j : I, Fin (blockCount (paths j).toFinset w)),
    (halfFiveReversePackedPaths paths w i).length) = _
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  let all := (paths i).toFinset
  let order := reversePackingOrder paths i
  let pos (v : V) := order.idxOf v
  have bounded (v : V) (on : v ∈ all) : pos v / w < blockCount all w := by
    have found := (protectedFirstPackingOrder_mem (reverseProtected_subset paths i)).mpr on
    have lt := List.idxOf_lt_length_of_mem found
    rw [protectedFirstPackingOrder_length (reverseProtected_subset paths i)] at lt
    exact Nat.lt_succ_of_le (Nat.div_le_div_right lt.le)
  have sumCount := card_eq_sum_card_fiberwise (s := all) (t := range (blockCount all w))
    (f := fun v => pos v / w) (fun v on => mem_range.mpr (bounded v on))
  have each (q : ℕ) : (reversePackedRow paths w i q).length = (all.filter (fun v => pos v / w = q)).card := by
    have sub : (reversePackedRow paths w i q).Sublist (paths i) := List.filter_sublist
    rw [← List.toFinset_card_of_nodup (sub.nodup (simple i))]
    apply congrArg card
    ext v
    simp [reversePackedRow,all,pos,order]
  calc
    _ = ∑ q : Fin (blockCount all w), (reversePackedRow paths w i q.val).length := rfl
    _ = ∑ q ∈ range (blockCount all w), (reversePackedRow paths w i q).length :=
      Fin.sum_univ_eq_sum_range (fun q => (reversePackedRow paths w i q).length) (blockCount all w)
    _ = (paths i).length := by
      simp only [each]
      exact sumCount.symm.trans (List.toFinset_card_of_nodup (simple i))

/-- A vertex gains no additional incidences from splitting rows into
these blocks, since only one block of its parent row contains it. -/
theorem halfFiveReversePackedPaths_degree (paths : I → List V) (w : ℕ) (v : V) :
    (occurrences (fun i => (halfFiveReversePackedPaths paths w i).toFinset) v).card ≤
      (occurrences (fun i => (paths i).toFinset) v).card := by
  let marks := fun i => (halfFiveReversePackedPaths paths w i).toFinset
  have occurs {i} (on : i ∈ occurrences marks v) : v ∈ halfFiveReversePackedPaths paths w i :=
    List.mem_toFinset.mp ((mem_occurrences (marks := marks)).mp on)
  apply card_le_card_of_injOn (fun i : ListBlockIndex paths w => i.fst)
  · intro i on
    exact mem_occurrences.mpr (List.mem_toFinset.mpr (mem_reversePackedPaths.mp (occurs on)).1)
  · intro i onI j onJ parent
    exact Classical.byContradiction fun diff => reversePackedPaths_disjoint diff parent (occurs onI) (occurs onJ)

end PathPacking

/-- With enough room for the protected rows and the protected path
vertices in their respective first blocks, both original-width packings
preserve half-five exclusion and all incidences before the final trimming. -/
theorem regularization_list_frozen_half_five_of_small_collision_and_reverse_supports {paths : Fin p → List (Fin n)}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (degreeRoom : let M := ∑ i, (paths i).length
      ∀ v, (halfFiveCollisionProtectedRows paths v).card ≤ 4*M/n)
    (pathRoom : let M := ∑ i, (paths i).length
      ∀ i, (halfFiveReverseProtectedVertices (halfFiveCollisionPackedPaths paths (4*M/n)) i).card ≤ 4*M/p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let copies := halfFiveCollisionPackedPaths paths D
  let pieces := halfFiveReversePackedPaths copies L
  obtain ⟨dPos,dTrim,_⟩ := four_average_width hn dense
  obtain ⟨lPos,lTrim,_⟩ := four_average_width hp long
  change 0 < D at dPos
  change 0 < L at lPos
  change 3*(M/D) ≤ n at dTrim
  change 3*(M/L) ≤ p at lTrim
  have copyMass : (∑ i, (copies i).length) = M := sum_congr rfl
    (fun i _ => by simp [copies,halfFiveCollisionPackedPaths])
  have copySimple (i : Fin p) : (copies i).Nodup := List.Nodup.of_map (fun v => v.fst)
    ((halfFiveCollisionPackedPaths_project paths D i).symm ▸ simple i)
  have piecesSimple (i : ListBlockIndex copies L) : (pieces i).Nodup :=
    (reversePackedPaths_sublist copies L i).nodup (copySimple i.fst)
  have vertices := (regularization_list_counts paths simple dPos lPos).1
  simp only [Fintype.card_fin] at vertices
  change Fintype.card (ListVertexBlockIndex paths D) ≤ n+M/D at vertices
  have vertexCap : 3*Fintype.card (ListVertexBlockIndex paths D) ≤ 4*n := by omega
  have families := blockIndex_card_precise (fun i => (copies i).toFinset) lPos
  simp only [Fintype.card_fin] at families
  have marksMass : (∑ i, (copies i).toFinset.card) = M :=
    (sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (copySimple i))).trans copyMass
  change Fintype.card (ListBlockIndex copies L) ≤ p+(∑ i, (copies i).toFinset.card)/L at families
  rw [marksMass] at families
  have pathCap : 3*Fintype.card (ListBlockIndex copies L) ≤ 4*p := by omega
  have freeCopies := halfFiveCollisionPackedPaths_halfFree simple free degreeRoom
  have freePieces := halfFiveReversePackedPaths_halfFree copySimple freeCopies pathRoom
  have mass : (∑ i, (pieces i).length) = M := (halfFiveReversePackedPaths_mass copies copySimple L).trans copyMass
  exact regularization_list_frozen_after_caps_with_room (half := true) (k := 5)
    pieces piecesSimple freePieces hn hp dense long vertexCap pathCap
    (halfFiveReversePackedPaths_length copySimple lPos)
    (fun v => (halfFiveReversePackedPaths_degree copies L v).trans (halfFiveCollisionPackedPaths_degree dPos v)) mass

end OnlineReachabilityPreservers
