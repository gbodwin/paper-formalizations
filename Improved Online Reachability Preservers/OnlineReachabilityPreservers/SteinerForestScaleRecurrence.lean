import OnlineReachabilityPreservers.SteinerBitOrders

/-! Compute the forest scale by a recurrence on vertex-indexed weights. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- The new root edge contributes its own weight and a copy of the
smaller rooted total for each vertex reaching the root. -/
def inwardHeightWeightRecurrence (G : Arcs V) (weight : V → V → ℕ) : ℕ → V → ℕ
  | 0, _ => 0
  | h+1, root => ∑ v ∈ reaches G root, (weight v root+inwardHeightWeightRecurrence G weight h v)

private def inwardHistoryEdgeWeight (G : Arcs V) (weight : V → V → ℕ) {h : ℕ}
    (root : V) (node : HeightNode V h) : ℕ :=
  if node.val ≠ [] ∧ heightHistoryValid G root node then
    weight (heightLabel root node) (heightLabel root (heightParent node))
  else 0

private theorem inwardHistoryEdgeWeight_cons (G : Arcs V) (weight : V → V → ℕ)
    {h : ℕ} (root head : V) (tail : HeightNode V h) :
    inwardHistoryEdgeWeight G weight root
      ((heightNodeFirst V h).symm (some (head,tail))) =
      if head ∈ reaches G root then
        (if tail.val = [] then weight head root else 0)+inwardHistoryEdgeWeight G weight head tail
      else 0 := by
  let lifted := (heightNodeFirst V h).symm (some (head,tail))
  change inwardHistoryEdgeWeight G weight root lifted =
    if head ∈ reaches G root then
      (if tail.val = [] then weight head root else 0)+inwardHistoryEdgeWeight G weight head tail
    else 0
  have liftedNE : lifted.val ≠ [] := by
    change head::tail.val ≠ []
    intro eq
    contradiction
  have valid : heightHistoryValid G root lifted ↔ head ∈ reaches G root ∧ heightHistoryValid G head tail :=
    List.isChain_cons_cons
  by_cases reachable : head ∈ reaches G root
  · by_cases empty : tail.val = []
    · have tailEq : tail = (heightRoot : HeightNode V h) := Subtype.ext empty
      have tailValid : heightHistoryValid G head tail := by
        rw [tailEq]
        exact List.isChain_singleton _
      have on : lifted.val ≠ [] ∧ heightHistoryValid G root lifted := ⟨liftedNE,valid.mpr ⟨reachable,tailValid⟩⟩
      have off : ¬ (tail.val ≠ [] ∧ heightHistoryValid G head tail) := fun z => z.1 empty
      have source : heightLabel root lifted = head := by
        simp [heightLabel,lifted,heightNodeFirst,empty]
      have target : heightLabel root (heightParent lifted) = root := by
        simp [heightLabel,heightParent,lifted,heightNodeFirst,empty]
      simp only [inwardHistoryEdgeWeight,ite_eq_left on,ite_eq_right off,ite_eq_left reachable,ite_eq_left empty,
        source,target,Nat.add_zero]
    · by_cases tailValid : heightHistoryValid G head tail
      · have on : lifted.val ≠ [] ∧ heightHistoryValid G root lifted := ⟨liftedNE,valid.mpr ⟨reachable,tailValid⟩⟩
        have tailOn : tail.val ≠ [] ∧ heightHistoryValid G head tail := ⟨empty,tailValid⟩
        have source : heightLabel root lifted = heightLabel head tail := by
          simp [heightLabel,lifted,heightNodeFirst]
        have target : heightLabel root (heightParent lifted) = heightLabel head (heightParent tail) := by
          simp [heightLabel,heightParent,lifted,heightNodeFirst,List.dropLast_cons_of_ne_nil empty]
        simp only [inwardHistoryEdgeWeight,ite_eq_left on,ite_eq_left tailOn,ite_eq_left reachable,ite_eq_right empty,
          source,target,Nat.zero_add]
      · have off : ¬ (lifted.val ≠ [] ∧ heightHistoryValid G root lifted) := fun z => tailValid (valid.mp z.2).2
        have tailOff : ¬ (tail.val ≠ [] ∧ heightHistoryValid G head tail) := fun z => tailValid z.2
        simp only [inwardHistoryEdgeWeight,ite_eq_right off,ite_eq_right tailOff,ite_eq_left reachable,
          ite_eq_right empty,Nat.zero_add]
  · have off : ¬ (lifted.val ≠ [] ∧ heightHistoryValid G root lifted) := fun z => reachable (valid.mp z.2).1
    simp only [inwardHistoryEdgeWeight,ite_eq_right off,ite_eq_right reachable]

omit [LinearOrder V] in
private theorem inwardHistoryEdgeWeight_empty_tail {h : ℕ} (head root : V) (weight : V → V → ℕ) :
    (∑ tail : HeightNode V h, if tail.val = [] then weight head root else 0) = weight head root := by
  rw [sum_eq_single (heightRoot : HeightNode V h)]
  · simp [heightRoot]
  · intro tail _ apart
    exact ite_eq_right (fun empty => apart (Subtype.ext empty))
  · simp

private theorem reaches_as_filter (G : Arcs V) (root : V) :
    (univ.filter fun v => v ∈ reaches G root) = reaches G root := by
  ext v
  simp

private theorem inwardHistoryEdgeWeight_sum (G : Arcs V) (weight : V → V → ℕ) (h : ℕ) (root : V) :
    (∑ node : HeightNode V h, inwardHistoryEdgeWeight G weight root node) =
      inwardHeightWeightRecurrence G weight h root := by
  induction h generalizing root with
  | zero =>
    rw [inwardHeightWeightRecurrence]
    apply sum_eq_zero
    intro node _
    have empty := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero node.property)
    simp [inwardHistoryEdgeWeight,empty]
  | succ h ih =>
    rw [inwardHeightWeightRecurrence,← reaches_as_filter G root,sum_filter]
    rw [← Equiv.sum_comp (heightNodeFirst V h).symm (inwardHistoryEdgeWeight G weight root)]
    rw [Fintype.sum_option,show inwardHistoryEdgeWeight G weight root
      ((heightNodeFirst V h).symm none) = 0 by rfl,zero_add,Fintype.sum_prod_type]
    apply sum_congr rfl
    intro head _
    simp only [inwardHistoryEdgeWeight_cons]
    by_cases reachable : head ∈ reaches G root
    · rw [ite_eq_left reachable]
      simp only [ite_eq_left reachable,sum_add_distrib,inwardHistoryEdgeWeight_empty_tail,ih]
    · simp [reachable]

/-- The recurrence equals the total weight of the actual finite
inward template, for an arbitrary supplied transfer weight. -/
theorem inwardHeightTree_weight_sum (G : Arcs V) (weight : V → V → ℕ) (h : ℕ) (root : V) :
    (∑ e ∈ inwardHeightTree G root h, weight (heightLabel root e.1) (heightLabel root e.2)) =
      inwardHeightWeightRecurrence G weight h root := by
  unfold inwardHeightTree
  rw [sum_image (fun _ _ _ _ same => congrArg Prod.fst same),sum_filter]
  exact inwardHistoryEdgeWeight_sum G weight h root

omit [Fintype V] in
private theorem heightJoin_root {h : ℕ} {root : V} {left right : Arcs (HeightNode V h)}
    {e : HeightForestVertex V h × HeightForestVertex V h} (member : e ∈ joinHeightCopies root left right) :
    heightForestRoot e.1 = root := by
  rcases mem_union.mp member with copies | center
  · rcases mem_union.mp copies with inside | inside
    · obtain ⟨a,_,rfl⟩ := mem_map.mp inside
      rfl
    · obtain ⟨a,_,rfl⟩ := mem_map.mp inside
      rfl
  · rw [mem_singleton.mp center]
    rfl

private theorem heightJoin_weight (G : Arcs V) {h : ℕ} (root : V)
    (left right : Arcs (HeightNode V h)) :
    (∑ e ∈ joinHeightCopies root left right, heightForestWeight G e) =
      (∑ e ∈ left, hops G (heightLabel root e.1) (heightLabel root e.2))+
        (∑ e ∈ right, hops G (heightLabel root e.2) (heightLabel root e.1)) := by
  let leftCopy := left.map ((heightCopy root false).prodMap (heightCopy root false))
  let rightCopy := (reverseArcs right).map ((heightCopy root true).prodMap (heightCopy root true))
  let center := heightForestRootLink root h
  have leftSides (e : HeightForestVertex V h × HeightForestVertex V h) (inside : e ∈ leftCopy) :
      heightForestSide e.1 = false ∧ heightForestSide e.2 = false := by
    obtain ⟨a,_,rfl⟩ := mem_map.mp inside
    exact ⟨rfl,rfl⟩
  have rightSides (e : HeightForestVertex V h × HeightForestVertex V h) (inside : e ∈ rightCopy) :
      heightForestSide e.1 = true ∧ heightForestSide e.2 = true := by
    obtain ⟨a,_,rfl⟩ := mem_map.mp inside
    exact ⟨rfl,rfl⟩
  have separate : Disjoint leftCopy rightCopy := disjoint_left.mpr fun e l r =>
    Bool.false_ne_true ((leftSides e l).1.symm.trans (rightSides e r).1)
  have central : Disjoint (leftCopy ∪ rightCopy) {center} := by
    apply disjoint_left.mpr
    intro e inside onCenter
    obtain rfl := mem_singleton.mp onCenter
    rcases mem_union.mp inside with l | r
    · exact (by decide : true ≠ false) (leftSides center l).2
    · exact Bool.false_ne_true (rightSides center r).1
  change (∑ e ∈ (leftCopy ∪ rightCopy) ∪ {center}, heightForestWeight G e) = _
  rw [sum_union central,sum_union separate,sum_singleton]
  have zero : heightForestWeight G center = 0 := hops_self G root
  rw [zero,add_zero]
  unfold leftCopy rightCopy reverseArcs
  rw [sum_map,sum_map,sum_image (fun _ _ _ _ eq => Prod.swap_injective eq)]
  rfl

/-- Sum rooted transfer weights in both orientations, using the same
graph distances in the forward direction of each transfer. -/
def forestScaleByRecurrence (G : Arcs V) (h : ℕ) : ℕ :=
  max 1 (∑ root,
    (inwardHeightWeightRecurrence G (hops G) h root+
      inwardHeightWeightRecurrence (reverseArcs G) (fun child parent => hops G parent child) h root))

/-- This recurrence computes the exact scale of the priced height
forest, including the unit floor and the zero-cost root attachments. -/
theorem forestScale_eq_recurrence (G : Arcs V) (h : ℕ) :
    forestScale G h = forestScaleByRecurrence G h := by
  unfold forestScale weightedCoverScale forestNetworkPriced forestScaleByRecurrence
  rw [sum_map]
  change max 1 (∑ e ∈ (heightForest G h).filter (fun e => 0 < heightForestWeight G e),
    heightForestWeight G e) = _
  rw [sum_filter]
  have dropZeros : (∑ e ∈ heightForest G h, if 0 < heightForestWeight G e then heightForestWeight G e else 0) =
      ∑ e ∈ heightForest G h, heightForestWeight G e := by
    apply sum_congr rfl
    intro e _
    split_ifs with positive
    · rfl
    · omega
  rw [dropZeros]
  unfold heightForest
  have unique : (↑(univ : Finset V) : Set V).PairwiseDisjoint (fun root =>
      joinHeightCopies root (inwardHeightTree G root h) (inwardHeightTree (reverseArcs G) root h)) := by
    intro a _ b _ apart
    apply disjoint_left.mpr
    intro e aMem bMem
    exact apart ((heightJoin_root aMem).symm.trans (heightJoin_root bMem))
  rw [sum_biUnion unique]
  apply congrArg (max 1)
  apply sum_congr rfl
  intro root _
  rw [heightJoin_weight, inwardHeightTree_weight_sum]
  congr 1
  exact inwardHeightTree_weight_sum (reverseArcs G) (fun child parent => hops G parent child) h root

end OnlineReachabilityPreservers
