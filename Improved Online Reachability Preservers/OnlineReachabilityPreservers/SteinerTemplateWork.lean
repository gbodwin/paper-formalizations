import OnlineReachabilityPreservers.SteinerHeightForest

/-! Account for reads of the distance table while validating all height histories. -/

namespace OnlineReachabilityPreservers

open Finset

private def orderedHistoryWork {V : Type*} (step : V → V → Bool × ℕ)
    (root : V) (path : List V) : Bool × ℕ :=
  match path with
  | [] => (true,0)
  | v::rest =>
    let first := step root v
    if first.1 then
      let suffix := orderedHistoryWork step v rest
      (suffix.1,first.2+suffix.2)
    else (false,first.2)

private theorem orderedHistoryWork_spec {V : Type*} (step : V → V → Bool × ℕ)
    (r : V → V → Prop) (same : ∀ a b, (step a b).1 = true ↔ r a b)
    (B : ℕ) (bound : ∀ a b, (step a b).2 ≤ B) (root : V) (path : List V) :
    let out := orderedHistoryWork step root path
    (out.1 = true ↔ (root::path).IsChain r) ∧ out.2 ≤ path.length*B := by
  induction path generalizing root with
  | nil => simp [orderedHistoryWork]
  | cons v rest ih =>
    have first := bound root v
    by_cases pass : (step root v).1 = true
    · have relation := (same root v).mp pass
      obtain ⟨right, count⟩ := ih v
      simp only [orderedHistoryWork, pass, ite_true, List.isChain_cons_cons, relation, true_and]
      refine ⟨right,?_⟩
      rw [List.length_cons, Nat.succ_mul, Nat.add_comm (rest.length*B)]
      exact Nat.add_le_add first count
    · have relation := (not_congr (same root v)).mp pass
      simp only [orderedHistoryWork, pass, ite_false, Bool.false_eq_true, List.isChain_cons_cons,
        relation, false_and, iff_self, true_and]
      simpa only [List.length_cons,Nat.succ_mul] using first.trans (Nat.le_add_left B (rest.length*B))

variable {V : Type*} [LinearOrder V] [Fintype V]

private def historyWithReadEntry (step : V → V → Bool × ℕ) (root : V) (height : ℕ) :
    HeightNode V height ↪ HeightNode V height × (Bool × ℕ) where
  toFun := fun node => (node, if node.val = [] then (false,0) else orderedHistoryWork step root node.val)
  inj' := fun _ _ equal => congrArg Prod.fst equal

/-- Build one inward tree with a metered lookup for each adjacent history label. -/
def inwardHeightTreeWithDistanceWork (step : V → V → Bool × ℕ) (root : V)
    (height : ℕ) : Arcs (HeightNode V height) × ℕ :=
  let rows := (univ : Finset (HeightNode V height)).map (historyWithReadEntry step root height)
  let arcs := (rows.filter fun e => e.2.1 = true).image fun e => (e.1,heightParent e.1)
  (arcs, ∑ r ∈ rows, r.2.2)

theorem inwardHeightTreeWithDistanceWork_spec (G : Arcs V) (step : V → V → Bool × ℕ)
    (same : ∀ a b, (step a b).1 = true ↔ Reach G b a) (B : ℕ)
    (bound : ∀ a b, (step a b).2 ≤ B) (root : V) (height : ℕ) :
    let out := inwardHeightTreeWithDistanceWork step root height
    out.1 = inwardHeightTree G root height ∧ out.2 ≤ Fintype.card (HeightNode V height)*height*B := by
  let entry := historyWithReadEntry step root height
  let rows := (univ : Finset (HeightNode V height)).map entry
  have details (node : HeightNode V height) :=
    orderedHistoryWork_spec step (fun a b => b ∈ reaches G a)
      (fun a b => (same a b).trans mem_reaches.symm) B bound root node.val
  have flag (node : HeightNode V height) : (entry node).2.1 = true ↔
      node.val ≠ [] ∧ heightHistoryValid G root node := by
    change (if node.val = [] then (false,0) else orderedHistoryWork step root node.val).1 = true ↔ _
    by_cases empty : node.val = []
    · simp [empty]
    · simpa [empty, heightHistoryValid] using (details node).1
  have amount (node : HeightNode V height) : (entry node).2.2 ≤ height*B := by
    change (if node.val = [] then (false,0) else orderedHistoryWork step root node.val).2 ≤ _
    by_cases empty : node.val = []
    · simp [empty]
    · simpa [empty] using
        (details node).2.trans (Nat.mul_le_mul_right _ node.property)
  constructor
  · change (rows.filter fun r => r.2.1 = true).image (fun r => (r.1,heightParent r.1)) = _
    ext e
    change _ ↔ e ∈ (univ.filter fun node : HeightNode V height =>
      node.val ≠ [] ∧ heightHistoryValid G root node).image (fun node => (node,heightParent node))
    constructor
    · intro h
      obtain ⟨record,present,rfl⟩ := mem_image.mp h
      obtain ⟨member,mark⟩ := mem_filter.mp present
      obtain ⟨node,_,rfl⟩ := mem_map.mp member
      exact mem_image.mpr ⟨node,mem_filter.mpr ⟨mem_univ _,(flag node).mp mark⟩,rfl⟩
    · intro h
      obtain ⟨node,found,rfl⟩ := mem_image.mp h
      exact mem_image.mpr ⟨entry node,
        mem_filter.mpr ⟨mem_map_of_mem _ (mem_univ node),(flag node).mpr (mem_filter.mp found).2⟩,rfl⟩
  · change (∑ r ∈ rows, r.2.2) ≤ _
    rw [sum_map]
    calc
      _ ≤ ∑ _ : HeightNode V height, height*B := sum_le_sum (fun node _ => amount node)
      _ = _ := by simp [Nat.mul_assoc, Nat.mul_comm]

private def pairedHeightWorkRow (left right : V → V → Bool × ℕ) (height : ℕ) :
    V ↪ V × (Arcs (HeightForestVertex V height) × ℕ) where
  toFun := fun r =>
    let L := inwardHeightTreeWithDistanceWork left r height
    let R := inwardHeightTreeWithDistanceWork right r height
    (r,joinHeightCopies r L.1 R.1,L.2+R.2)
  inj' := fun _ _ equal => congrArg Prod.fst equal

/-- Build the paired forest once from metered original-distance reads. -/
def heightForestWithDistanceWork (left right : V → V → Bool × ℕ) (height : ℕ) :
    Arcs (HeightForestVertex V height) × ℕ :=
  let rows := univ.map (pairedHeightWorkRow left right height)
  (rows.biUnion (fun r => r.2.1), ∑ r ∈ rows, r.2.2)

theorem heightForestWithDistanceWork_spec (G : Arcs V) (left right : V → V → Bool × ℕ)
    (L : ∀ a b, (left a b).1 = true ↔ Reach G b a)
    (R : ∀ a b, (right a b).1 = true ↔ Reach (reverseArcs G) b a)
    (B : ℕ) (lB : ∀ a b, (left a b).2 ≤ B) (rB : ∀ a b, (right a b).2 ≤ B)
    (height : ℕ) :
    let out := heightForestWithDistanceWork left right height
    out.1 = heightForest G height ∧
      out.2 ≤ Fintype.card V*(2*Fintype.card (HeightNode V height)*height*B) := by
  let entry := pairedHeightWorkRow left right height
  let rows := (univ : Finset V).map entry
  have each (r : V) :
      (entry r).2.1 = joinHeightCopies r (inwardHeightTree G r height)
        (inwardHeightTree (reverseArcs G) r height) ∧
      (entry r).2.2 ≤ 2*Fintype.card (HeightNode V height)*height*B := by
    obtain ⟨leftEq,leftBound⟩ := inwardHeightTreeWithDistanceWork_spec G left L B lB r height
    obtain ⟨rightEq,rightBound⟩ := inwardHeightTreeWithDistanceWork_spec (reverseArcs G) right R B rB r height
    refine ⟨congrArg₂ (joinHeightCopies r) leftEq rightEq, ?_⟩
    exact (Nat.add_le_add leftBound rightBound).trans_eq (by ring)
  constructor
  · change rows.biUnion (fun r => r.2.1) = _
    ext e
    unfold heightForest
    constructor
    · intro member
      obtain ⟨r,present,inCopy⟩ := mem_biUnion.mp member
      obtain ⟨root,_,rfl⟩ := mem_map.mp present
      exact mem_biUnion.mpr ⟨root,mem_univ _,(each root).1 ▸ inCopy⟩
    · intro member
      obtain ⟨root,_,inCopy⟩ := mem_biUnion.mp member
      exact mem_biUnion.mpr ⟨entry root,mem_map_of_mem _ (mem_univ _),(each root).1.symm ▸ inCopy⟩
  · change (∑ r ∈ rows, r.2.2) ≤ _
    rw [sum_map]
    calc
      _ ≤ ∑ _r : V, 2*Fintype.card (HeightNode V height)*height*B :=
        sum_le_sum (fun r _ => (each r).2)
      _ = _ := by simp [Nat.mul_comm]

end OnlineReachabilityPreservers
