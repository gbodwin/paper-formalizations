import OnlineReachabilityPreservers.ComponentSplitCleaning
import OnlineReachabilityPreservers.HalfFiveTerminalRank
import OnlineReachabilityPreservers.HalfFiveDegreeRepair
import Mathlib.Data.Finset.Sort

/-! Protected degree and length blocks for half-five patterns and short backward returns. -/

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

private noncomputable def protectedPathPackingOrder (paths : I → List V) (protect : I → Finset V) (i : I) : List V :=
  protectedFirstPackingOrder (paths i).toFinset (protect i)

private noncomputable def protectedPackedRow (paths : I → List V) (protect : I → Finset V) (w : ℕ) (i : I) (q : ℕ) : List V :=
  (paths i).filter fun v => decide ((protectedPathPackingOrder paths protect i).idxOf v / w = q)

/-- Assign width blocks with the protected endpoints first, and retain
the original comparison order within each piece. -/
noncomputable def protectedPackedPaths (paths : I → List V) (protect : I → Finset V) (w : ℕ)
    (i : ListBlockIndex paths w) : List V :=
  protectedPackedRow paths protect w i.fst i.snd.val

omit [LinearOrder I] [Fintype I] in
private theorem protectedPackedPaths_sublist (paths : I → List V) (protect : I → Finset V) (w : ℕ) (i : ListBlockIndex paths w) :
    (protectedPackedPaths paths protect w i).Sublist (paths i.fst) := List.filter_sublist

omit [LinearOrder I] [Fintype I] in
private theorem mem_protectedPackedPaths {paths : I → List V} {protect : I → Finset V} {w : ℕ} {i : ListBlockIndex paths w} {v : V} :
    v ∈ protectedPackedPaths paths protect w i ↔ v ∈ paths i.fst ∧ (protectedPathPackingOrder paths protect i.fst).idxOf v / w = i.snd.val := by
  simp [protectedPackedPaths,protectedPackedRow]

omit [LinearOrder I] [Fintype I] in
private theorem protectedPackedPaths_same_of_label {paths : I → List V} {w : ℕ}
    {i j : ListBlockIndex paths w}
    (parent : i.fst = j.fst) (block : i.snd.val = j.snd.val) : i = j := by
  rcases i with ⟨i,a⟩
  rcases j with ⟨j,b⟩
  change i = j at parent
  subst j
  change a.val = b.val at block
  have equal : a = b := Fin.ext block
  subst b
  rfl

omit [LinearOrder I] [Fintype I] in
private theorem protectedPackedPaths_disjoint {paths : I → List V} {protect : I → Finset V} {w : ℕ} {i j : ListBlockIndex paths w} {v : V}
    (different : i ≠ j) (parent : i.fst = j.fst) (left : v ∈ protectedPackedPaths paths protect w i)
    (right : v ∈ protectedPackedPaths paths protect w j) : False := by
  have fromI := (mem_protectedPackedPaths.mp left).2
  have fromJ := (mem_protectedPackedPaths.mp right).2
  have compares := congrArg (fun a => (protectedPathPackingOrder paths protect a).idxOf v / w) parent
  exact different (protectedPackedPaths_same_of_label parent (fromI.symm.trans (compares.trans fromJ)))

omit [LinearOrder I] [Fintype I] in
private theorem protectedPackedPaths_same_for_protected {paths : I → List V} {protect : I → Finset V}
    {w : ℕ} {i j : ListBlockIndex paths w} {x y : V}
    (room : (protect i.fst).card ≤ w) (parent : i.fst = j.fst)
    (selectedX : x ∈ protect i.fst) (selectedY : y ∈ protect i.fst)
    (onI : x ∈ protectedPackedPaths paths protect w i)
    (onJ : y ∈ protectedPackedPaths paths protect w j) : i = j := by
  have blockX : (protectedPathPackingOrder paths protect i.fst).idxOf x / w = 0 :=
    Nat.div_eq_of_lt ((protectedFirstPackingOrder_forced_position selectedX).trans_le room)
  have blockY : (protectedPathPackingOrder paths protect i.fst).idxOf y / w = 0 :=
    Nat.div_eq_of_lt ((protectedFirstPackingOrder_forced_position selectedY).trans_le room)
  have atI := (mem_protectedPackedPaths.mp onI).2
  have atJ := (mem_protectedPackedPaths.mp onJ).2
  have compares := congrArg (fun a => (protectedPathPackingOrder paths protect a).idxOf y / w) parent
  rw [blockX] at atI
  exact protectedPackedPaths_same_of_label parent (atI.symm.trans (blockY.symm.trans (compares.trans atJ)))

omit [LinearOrder I] [Fintype I] in
/-- Each path piece also respects the block width. -/
theorem protectedPackedPaths_length {paths : I → List V} {protect : I → Finset V} {w : ℕ}
    (contained : ∀ i, protect i ⊆ (paths i).toFinset)
    (simple : ∀ i, (paths i).Nodup) (width : 0 < w) (i : ListBlockIndex paths w) :
    (protectedPackedPaths paths protect w i).length ≤ w := by
  have pieceSimple := (protectedPackedPaths_sublist paths protect w i).nodup (simple i.fst)
  rw [← List.toFinset_card_of_nodup pieceSimple]
  apply packingOrder_block_card (protectedPathPackingOrder paths protect i.fst) width i.snd.val
  intro v on
  obtain ⟨original,r⟩ := mem_protectedPackedPaths.mp (List.mem_toFinset.mp on)
  exact ⟨(protectedFirstPackingOrder_mem (contained i.fst)).mpr (List.mem_toFinset.mpr original),r⟩

omit [LinearOrder I] in
/-- Splitting only partitions the incidences of each row. -/
theorem protectedPackedPaths_mass (paths : I → List V) (protect : I → Finset V)
    (contained : ∀ i, protect i ⊆ (paths i).toFinset) (simple : ∀ i, (paths i).Nodup) (w : ℕ) :
    (∑ i, (protectedPackedPaths paths protect w i).length) = ∑ i, (paths i).length := by
  change (∑ i : (Σ j : I, Fin (blockCount (paths j).toFinset w)),
    (protectedPackedPaths paths protect w i).length) = _
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  let all := (paths i).toFinset
  let order := protectedPathPackingOrder paths protect i
  let pos (v : V) := order.idxOf v
  have bounded (v : V) (on : v ∈ all) : pos v / w < blockCount all w := by
    have found := (protectedFirstPackingOrder_mem (contained i)).mpr on
    have lt := List.idxOf_lt_length_of_mem found
    rw [protectedFirstPackingOrder_length (contained i)] at lt
    exact Nat.lt_succ_of_le (Nat.div_le_div_right lt.le)
  have sumCount := card_eq_sum_card_fiberwise (s := all) (t := range (blockCount all w))
    (f := fun v => pos v / w) (fun v on => mem_range.mpr (bounded v on))
  have each (q : ℕ) : (protectedPackedRow paths protect w i q).length = (all.filter (fun v => pos v / w = q)).card := by
    have sub : (protectedPackedRow paths protect w i q).Sublist (paths i) := List.filter_sublist
    rw [← List.toFinset_card_of_nodup (sub.nodup (simple i))]
    apply congrArg card
    ext v
    simp [protectedPackedRow,all,pos,order]
  calc
    _ = ∑ q : Fin (blockCount all w), (protectedPackedRow paths protect w i q.val).length := rfl
    _ = ∑ q ∈ range (blockCount all w), (protectedPackedRow paths protect w i q).length :=
      Fin.sum_univ_eq_sum_range (fun q => (protectedPackedRow paths protect w i q).length) (blockCount all w)
    _ = (paths i).length := by
      simp only [each]
      exact sumCount.symm.trans (List.toFinset_card_of_nodup (simple i))

omit [LinearOrder I] in
/-- A vertex gains no additional incidences from splitting rows into
these blocks, since only one block of its parent row contains it. -/
theorem protectedPackedPaths_degree (paths : I → List V) (protect : I → Finset V) (w : ℕ) (v : V) :
    (occurrences (fun i => (protectedPackedPaths paths protect w i).toFinset) v).card ≤
      (occurrences (fun i => (paths i).toFinset) v).card := by
  let marks := fun i => (protectedPackedPaths paths protect w i).toFinset
  have occurs {i} (on : i ∈ occurrences marks v) : v ∈ protectedPackedPaths paths protect w i :=
    List.mem_toFinset.mp ((mem_occurrences (marks := marks)).mp on)
  apply card_le_card_of_injOn (fun i : ListBlockIndex paths w => i.fst)
  · intro i on
    exact mem_occurrences.mpr (List.mem_toFinset.mpr (mem_protectedPackedPaths.mp (occurs on)).1)
  · intro i onI j onJ parent
    exact Classical.byContradiction fun diff => protectedPackedPaths_disjoint diff parent (occurs onI) (occurs onJ)

/-- Protect both endpoints of every comparison reversed on another row. -/
noncomputable def halfFiveReverseProtectedVertices (paths : I → List V) (i : I) : Finset V := by
  classical
  exact (paths i).toFinset.filter fun x => ∃ j, i ≠ j ∧ ∃ y,
    (Before paths i x y ∧ Before paths j y x) ∨ (Before paths i y x ∧ Before paths j x y)

private theorem reverseProtected_pair {paths : I → List V} {i j : I} {x y : V}
    (different : i ≠ j) (forward : Before paths i x y) (backward : Before paths j y x) :
    x ∈ halfFiveReverseProtectedVertices paths i ∧ y ∈ halfFiveReverseProtectedVertices paths i := by
  classical
  exact ⟨mem_filter.mpr ⟨List.mem_toFinset.mpr forward.1,j,different,y,Or.inl ⟨forward,backward⟩⟩,
    mem_filter.mpr ⟨List.mem_toFinset.mpr forward.2.1,j,different,x,Or.inr ⟨forward,backward⟩⟩⟩

/-- Assign width blocks with reversed endpoints first and retain the
original comparison order within each piece. -/
noncomputable def halfFiveReversePackedPaths (paths : I → List V) (w : ℕ)
    (i : ListBlockIndex paths w) : List V :=
  protectedPackedPaths paths (halfFiveReverseProtectedVertices paths) w i

private theorem reverseProtected_subset (paths : I → List V) (i : I) :
    halfFiveReverseProtectedVertices paths i ⊆ (paths i).toFinset := by
  classical
  exact filter_subset _ _

/-- Each path piece also respects the block width. -/
theorem halfFiveReversePackedPaths_length {paths : I → List V} {w : ℕ}
    (simple : ∀ i, (paths i).Nodup) (width : 0 < w) (i : ListBlockIndex paths w) :
    (halfFiveReversePackedPaths paths w i).length ≤ w :=
  protectedPackedPaths_length (reverseProtected_subset paths) simple width i

/-- Splitting only partitions the incidences of each row. -/
theorem halfFiveReversePackedPaths_mass (paths : I → List V) (simple : ∀ i, (paths i).Nodup) (w : ℕ) :
    (∑ i, (halfFiveReversePackedPaths paths w i).length) = ∑ i, (paths i).length :=
  protectedPackedPaths_mass paths _ (reverseProtected_subset paths) simple w

/-- A vertex gains no additional incidences from splitting rows into
these blocks, since only one block of its parent row contains it. -/
theorem halfFiveReversePackedPaths_degree (paths : I → List V) (w : ℕ) (v : V) :
    (occurrences (fun i => (halfFiveReversePackedPaths paths w i).toFinset) v).card ≤
      (occurrences (fun i => (paths i).toFinset) v).card :=
  protectedPackedPaths_degree paths _ w v

/-- Packing the protected endpoints together preserves half-five through
these possibly noncontiguous path splits. -/
theorem halfFiveReversePackedPaths_halfFree {paths : I → List V} {w : ℕ}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5)
    (room : ∀ i, (halfFiveReverseProtectedVertices paths i).card ≤ w) :
    HalfBridgeFree (Before (halfFiveReversePackedPaths paths w)) 5 := by
  let pieces := halfFiveReversePackedPaths paths w
  have step {i x y} (on : Before pieces i x y) : Before paths i.fst x y :=
    listBefore_of_sublist (paths := fun a : ListBlockIndex paths w => paths a.fst) (cut := pieces)
      (simple i.fst) (protectedPackedPaths_sublist paths (halfFiveReverseProtectedVertices paths) w i) on
  have together {i j q : ListBlockIndex paths w} {x y : V} (parent : i.fst = j.fst)
      (apart : i.fst ≠ q.fst) (forward : Before paths i.fst x y) (backward : Before pieces q y x)
      (onI : x ∈ pieces i) (onJ : y ∈ pieces j) : i = j := by
    obtain ⟨xProtected,yProtected⟩ := reverseProtected_pair apart forward (step backward)
    exact protectedPackedPaths_same_for_protected (room i.fst) parent xProtected yProtected onI onJ
  intro d small b earlier
  let old := listBridge_after_opposite_safe_split_through_five Sigma.fst (fun {_ _ _} => step)
    (fun {_ _ _} => protectedPackedPaths_disjoint)
    (fun _ {_ _ _ _} diff left right => no_parallel_list_steps free (by decide) diff left right)
    (fun _ {_ _ _ _ _} => together) (by omega) b
  apply free small old
  exact lt_of_le_of_ne (block_parent_mono (fun i => (paths i).toFinset) w earlier.le) (old.river_ne_arc _).symm

end PathPacking

/-- With the original path width, mass-preserving path packing expands
the support by at most the allowance for the final trimming. -/
theorem regularization_list_frozen_after_protected_path_packing {V : Type*} [LinearOrder V] [Fintype V]
    {n p k M : ℕ} {half : Bool} (rows : Fin p → List V) (protect : Fin p → Finset V)
    (contained : ∀ i, protect i ⊆ (rows i).toFinset) (simple : ∀ i, (rows i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (vertexCap : 3*Fintype.card V ≤ 4*n)
    (degree : ∀ v, (occurrences (fun i => (rows i).toFinset) v).card ≤ 4*M/n)
    (mass : (∑ i, (rows i).length) = M)
    (legal : localOrderAdmissible half k (protectedPackedPaths rows protect (4*M/p))) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let L := 4*M/p
  let pieces := protectedPackedPaths rows protect L
  obtain ⟨positive, room, _⟩ := four_average_width hp long
  change 0 < L at positive
  change 3*(M/L) ≤ p at room
  have piecesSimple (i : ListBlockIndex rows L) : (pieces i).Nodup :=
    (protectedPackedPaths_sublist rows protect L i).nodup (simple i.fst)
  have families := blockIndex_card_precise (fun i => (rows i).toFinset) positive
  simp only [Fintype.card_fin] at families
  have marksMass : (∑ i, (rows i).toFinset.card) = M :=
    (sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (simple i))).trans mass
  change Fintype.card (ListBlockIndex rows L) ≤ p + (∑ i, (rows i).toFinset.card)/L at families
  rw [marksMass] at families
  have pathCap : 3*Fintype.card (ListBlockIndex rows L) ≤ 4*p := by omega
  exact regularization_list_frozen_after_caps_with_room pieces piecesSimple legal hn hp dense long vertexCap pathCap
    (protectedPackedPaths_length contained simple positive)
    (fun v => (protectedPackedPaths_degree rows protect L v).trans (degree v))
    ((protectedPackedPaths_mass rows protect contained simple L).trans mass)

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
  let copies := halfFiveCollisionPackedPaths paths D
  obtain ⟨dPos, dTrim, _⟩ := four_average_width hn dense
  obtain ⟨lPos, _, _⟩ := four_average_width hp long
  change 0 < D at dPos
  change 3*(M/D) ≤ n at dTrim
  have copyMass : (∑ i, (copies i).length) = M := sum_congr rfl
    (fun i _ => by simp [copies, halfFiveCollisionPackedPaths])
  have copySimple (i : Fin p) : (copies i).Nodup := List.Nodup.of_map (fun v => v.fst)
    ((halfFiveCollisionPackedPaths_project paths D i).symm ▸ simple i)
  have vertices := (regularization_list_counts paths simple dPos lPos).1
  simp only [Fintype.card_fin] at vertices
  change Fintype.card (ListVertexBlockIndex paths D) ≤ n + M/D at vertices
  have vertexCap : 3*Fintype.card (ListVertexBlockIndex paths D) ≤ 4*n := by omega
  have freeCopies := halfFiveCollisionPackedPaths_halfFree simple free degreeRoom
  have freePieces := halfFiveReversePackedPaths_halfFree copySimple freeCopies pathRoom
  exact regularization_list_frozen_after_protected_path_packing (half := true) (k := 5)
    copies _ (reverseProtected_subset copies) copySimple hn hp dense long vertexCap
    (halfFiveCollisionPackedPaths_degree dPos) copyMass freePieces

section ReturnPacking

variable {I V : Type*} [LinearOrder I] [Fintype I] [LinearOrder V] [Fintype V]

/-- Protect both endpoints of every row comparison with a backward
route through the specified radius in the copied precedence graph. -/
noncomputable def shortReturnProtectedVertices (paths : I → List V) (radius : ℕ) (i : I) : Finset V := by
  classical
  let G := listPiecePrecedenceGraph paths
  exact (paths i).toFinset.filter fun x => ∃ y,
    (Before paths i x y ∧ y ∈ reachIn G x radius) ∨ (Before paths i y x ∧ x ∈ reachIn G y radius)

omit [LinearOrder I] in
theorem shortReturnProtectedVertices_subset (paths : I → List V) (radius : ℕ) (i : I) :
    shortReturnProtectedVertices paths radius i ⊆ (paths i).toFinset := by
  classical
  exact filter_subset _ _

omit [LinearOrder I] in
private theorem shortReturnProtectedVertices_pair {paths : I → List V} {radius : ℕ} {i : I} {x y : V}
    (before : Before paths i x y) (back : y ∈ reachIn (listPiecePrecedenceGraph paths) x radius) :
    x ∈ shortReturnProtectedVertices paths radius i ∧ y ∈ shortReturnProtectedVertices paths radius i := by
  classical
  exact ⟨mem_filter.mpr ⟨List.mem_toFinset.mpr before.1, y, Or.inl ⟨before, back⟩⟩,
    mem_filter.mpr ⟨List.mem_toFinset.mpr before.2.1, x, Or.inr ⟨before, back⟩⟩⟩

/-- Assign path blocks by protecting short-return endpoints together
and keep the original comparison order within each block. -/
noncomputable def shortReturnPackedPaths (paths : I → List V) (w cutoff : ℕ)
    (i : ListBlockIndex paths w) : List V :=
  protectedPackedPaths paths (shortReturnProtectedVertices paths (cutoff - 3)) w i

/-- Placing all short-return endpoints in block zero preserves full or
half exclusion through the given cutoff on the copied rows. -/
theorem shortReturnPackedPaths_admissible {paths : I → List V} {w cutoff : ℕ} {half : Bool}
    (simple : ∀ i, (paths i).Nodup) (free : localOrderAdmissible half cutoff paths)
    (room : ∀ i, (shortReturnProtectedVertices paths (cutoff - 3) i).card ≤ w) :
    localOrderAdmissible half cutoff (shortReturnPackedPaths paths w cutoff) := by
  let pieces := shortReturnPackedPaths paths w cutoff
  let G := listPiecePrecedenceGraph paths
  let parent (i : ListBlockIndex paths w) := i.fst
  have step ⦃i x y⦄ (on : Before pieces i x y) : Before paths (parent i) x y :=
    listBefore_of_sublist (paths := fun j : ListBlockIndex paths w => paths j.fst) (cut := pieces)
      (simple i.fst) (protectedPackedPaths_sublist paths _ w i) on
  have projects ⦃i x y⦄ (on : Before pieces i x y) : Edge G (id x) (id y) :=
    listPiecePrecedenceGraph_edge.mpr ⟨parent i, step on⟩
  have disjoint ⦃i j x⦄ (apart : i ≠ j) (same : parent i = parent j)
      (left : x ∈ pieces i) (right : x ∈ pieces j) : False :=
    protectedPackedPaths_disjoint apart same left right
  have safe : NoShortBackwardReturnAcrossPieces G id paths pieces parent (cutoff - 3) := by
    intro i j x y apart same left right before back
    obtain ⟨protectedX, protectedY⟩ := shortReturnProtectedVertices_pair before back
    exact apart (protectedPackedPaths_same_for_protected (room i.fst) same protectedX protectedY left right)
  cases half
  · exact bridgeFree_of_disjoint_split_of_no_backward_returns G id free parent step projects disjoint safe
  · exact halfBridgeFree_of_disjoint_split_of_no_backward_returns G id free parent
      (block_parent_mono (fun i => (paths i).toFinset) w) step projects disjoint safe

end ReturnPacking

/-- After legal standard degree copying, a path packing with room for the
short-return endpoints gives both original budgets, all four frozen
caps, and mass at least one sixteenth of the original mass. -/
theorem regularization_list_frozen_of_small_short_return_supports {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (copyLegal : let M := ∑ i, (paths i).length; localOrderAdmissible half k (splitListVertices paths (4*M/n)))
    (room : let M := ∑ i, (paths i).length
      ∀ i, (shortReturnProtectedVertices (splitListVertices paths (4*M/n)) (k - 3) i).card ≤ 4*M/p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let copies := splitListVertices paths D
  obtain ⟨dPos, dTrim, _⟩ := four_average_width hn dense
  obtain ⟨lPos, _, _⟩ := four_average_width hp long
  change 0 < D at dPos
  change 3*(M/D) ≤ n at dTrim
  have copyMass : (∑ i, (copies i).length) = M :=
    sum_congr rfl (fun i _ => by simp [copies, splitListVertices])
  have copySimple (i : Fin p) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have vertices := (regularization_list_counts paths simple dPos lPos).1
  simp only [Fintype.card_fin] at vertices
  change Fintype.card (ListVertexBlockIndex paths D) ≤ n + M/D at vertices
  have vertexCap : 3*Fintype.card (ListVertexBlockIndex paths D) ≤ 4*n := by omega
  have degree (v : ListVertexBlockIndex paths D) : (occurrences (fun i => (copies i).toFinset) v).card ≤ D := by
    simpa only [copies, splitListVertices_toFinset] using
      (splitVertices_degree (fun i => (paths i).toFinset) dPos v)
  exact regularization_list_frozen_after_protected_path_packing copies _
    (shortReturnProtectedVertices_subset copies (k - 3)) copySimple hn hp dense long vertexCap degree copyMass
    (shortReturnPackedPaths_admissible copySimple copyLegal room)

end OnlineReachabilityPreservers
