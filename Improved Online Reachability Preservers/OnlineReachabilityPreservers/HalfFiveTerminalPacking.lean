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

private noncomputable def collisionPackingOrder (paths : Fin p → List (Fin n)) (v : Fin n) : List (Fin p) :=
  let forced := halfFiveCollisionProtectedRows paths v
  let all := occurrences (fun i => (paths i).toFinset) v
  forced.sort (· ≤ ·) ++ (all \ forced).sort (· ≤ ·)

private theorem collisionPackingOrder_mem {paths : Fin p → List (Fin n)} {v : Fin n} {i : Fin p} :
    i ∈ collisionPackingOrder paths v ↔ i ∈ occurrences (fun j => (paths j).toFinset) v := by
  classical
  unfold collisionPackingOrder
  simp only [List.mem_append,mem_sort,mem_sdiff]
  constructor
  · exact fun h => h.elim (fun on => collisionProtected_subset paths v on) And.left
  · intro on
    by_cases forced : i ∈ halfFiveCollisionProtectedRows paths v
    · exact Or.inl forced
    · exact Or.inr ⟨on,forced⟩

private theorem collisionPackingOrder_length (paths : Fin p → List (Fin n)) (v : Fin n) :
    (collisionPackingOrder paths v).length = (occurrences (fun j => (paths j).toFinset) v).card := by
  unfold collisionPackingOrder
  simp only [List.length_append,length_sort]
  rw [Nat.add_comm]
  exact card_sdiff_add_card_eq_card (collisionProtected_subset paths v)

private theorem collisionPackingOrder_forced_position {paths : Fin p → List (Fin n)} {v : Fin n} {i : Fin p}
    (forced : i ∈ halfFiveCollisionProtectedRows paths v) :
    (collisionPackingOrder paths v).idxOf i < (halfFiveCollisionProtectedRows paths v).card := by
  let first := (halfFiveCollisionProtectedRows paths v).sort (· ≤ ·)
  have present : i ∈ first := (mem_sort _).mpr forced
  unfold collisionPackingOrder
  rw [List.idxOf_append_of_mem present,← length_sort (r := (· ≤ ·))]
  exact List.idxOf_lt_length_of_mem present

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
  let uses := occurrences (fun i => (halfFiveCollisionPackedPaths paths D i).toFinset) v
  let order := collisionPackingOrder paths v.fst
  let pos (i : Fin p) := order.idxOf i
  have atCopy (i) (seen : i ∈ uses) : i ∈ order ∧ pos i / D = v.snd.val := by
    have present : v ∈ halfFiveCollisionPackedPaths paths D i := List.mem_toFinset.mp
      ((mem_occurrences (marks := fun j => (halfFiveCollisionPackedPaths paths D j).toFinset)).mp seen)
    have on := collisionPackedPaths_mem present
    exact ⟨collisionPackingOrder_mem.mpr (mem_occurrences.mpr (List.mem_toFinset.mpr on.1)),on.2.symm⟩
  calc
    uses.card ≤ (range D).card := by
      apply card_le_card_of_injOn (fun i => pos i % D)
      · intro i _
        exact mem_range.mpr (Nat.mod_lt _ positive)
      · intro i inI j inJ equal
        obtain ⟨listedI,inBlockI⟩ := atCopy i inI
        obtain ⟨listedJ,inBlockJ⟩ := atCopy j inJ
        change pos i % D = pos j % D at equal
        have first := Nat.mod_add_div (pos i) D
        have second := Nat.mod_add_div (pos j) D
        rw [inBlockI] at first
        rw [inBlockJ] at second
        have same : pos i = pos j := by omega
        have left : order[pos i]'(List.idxOf_lt_length_of_mem listedI) = i :=
          List.getElem_idxOf (List.idxOf_lt_length_of_mem listedI)
        have right : order[pos j]'(List.idxOf_lt_length_of_mem listedJ) = j :=
          List.getElem_idxOf (List.idxOf_lt_length_of_mem listedJ)
        exact left.symm.trans (by simpa only [same] using right)
    _ = D := card_range D

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

end OnlineReachabilityPreservers
