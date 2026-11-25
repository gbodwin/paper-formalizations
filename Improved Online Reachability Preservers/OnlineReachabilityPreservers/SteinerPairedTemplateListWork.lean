import OnlineReachabilityPreservers.SteinerHistoryEnumerationWork
import OnlineReachabilityPreservers.SteinerTemplateListWork

/-! Build the paired forest with one shared list of histories and explicit arc construction. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

private def inwardCopyArc {h : ℕ} (root : V) :
    HeightNode V h × HeightNode V h → HeightForestVertex V h × HeightForestVertex V h :=
  (heightCopy root false).prodMap (heightCopy root false)

private def outwardCopyArc {h : ℕ} (root : V) :
    HeightNode V h × HeightNode V h → HeightForestVertex V h × HeightForestVertex V h :=
  fun e => (heightCopy root true e.2,heightCopy root true e.1)

private def prependCopyArcsWithWordWork {A B : Type*} (copy : A → B) (tail : List B) : List A → List B × ℕ
  | [] => (tail,3)
  | edge::next =>
    let remaining := prependCopyArcsWithWordWork copy tail next
    (copy edge::remaining.1,remaining.2+12)

private theorem prependCopyArcsWithWordWork_spec {A B : Type*} (copy : A → B) (tail : List B) (rows : List A) :
    let made := prependCopyArcsWithWordWork copy tail rows
    made.1 = rows.map copy ++ tail ∧ made.2 = 12*rows.length+3 := by
  induction rows with
  | nil => simp [prependCopyArcsWithWordWork]
  | cons e rest ih =>
    obtain ⟨same,tally⟩ := ih
    simp [prependCopyArcsWithWordWork, same, tally, List.length_cons, Nat.mul_succ]

omit [LinearOrder V] [Fintype V] in
private theorem inwardTemplateListWithWordWork_length {h : ℕ} (step : V → V → Bool × ℕ)
    (root : V) (nodes : List (HeightNode V h)) :
    (inwardTemplateListWithWordWork step root nodes).1.length ≤ nodes.length := by
  induction nodes with
  | nil => simp [inwardTemplateListWithWordWork]
  | cons node rest ih =>
    rw [inwardTemplateListWithWordWork]
    cases shape : node.val with
    | nil => exact ih.trans (Nat.le_succ _)
    | cons v suffix =>
      dsimp only
      split
      · exact Nat.succ_le_succ ih
      · exact ih.trans (Nat.le_succ _)

/-- The two directed copies are appended with their free root link. The shared
history list is reused for every root and both directions. -/
def pairedTemplateListWithWordWork {h : ℕ} (left right : V → V → Bool × ℕ) (histories : List (HeightNode V h)) :
    List V → List (HeightForestVertex V h × HeightForestVertex V h) × ℕ
  | [] => ([],3)
  | root::roots =>
    let rest := pairedTemplateListWithWordWork left right histories roots
    let L := inwardTemplateListWithWordWork left root histories
    let R := inwardTemplateListWithWordWork right root histories
    let withRight := prependCopyArcsWithWordWork (outwardCopyArc root) rest.1 R.1
    let withLeft := prependCopyArcsWithWordWork (inwardCopyArc root) withRight.1 L.1
    (heightForestRootLink root h::withLeft.1,rest.2+L.2+R.2+withRight.2+withLeft.2+20)

omit [Fintype V] in
private theorem mapCopy_inward {h : ℕ} (root : V) (rows : List (HeightNode V h × HeightNode V h)) :
    (rows.map (inwardCopyArc root)).toFinset =
      rows.toFinset.map ((heightCopy root false).prodMap (heightCopy root false)) := by
  ext e
  simp [inwardCopyArc, mem_map]

omit [Fintype V] in
private theorem mapCopy_outward {h : ℕ} (root : V) (rows : List (HeightNode V h × HeightNode V h)) :
    (rows.map (outwardCopyArc root)).toFinset =
      (reverseArcs rows.toFinset).map ((heightCopy root true).prodMap (heightCopy root true)) := by
  ext e
  simp only [List.mem_toFinset, List.mem_map, mem_map, reverseArcs, mem_image]
  constructor
  · rintro ⟨row,on,rfl⟩
    exact ⟨row.swap,⟨row,on,rfl⟩,rfl⟩
  · rintro ⟨row,⟨source,on,rfl⟩,rfl⟩
    exact ⟨source,on,rfl⟩

private theorem pairedTemplateListWithWordWork_partial {h : ℕ} (G : Arcs V)
    (left right : V → V → Bool × ℕ)
    (sameL : ∀ a b, (left a b).1 = true ↔ Reach G b a)
    (sameR : ∀ a b, (right a b).1 = true ↔ Reach (reverseArcs G) b a)
    (B : ℕ) (budgetL : ∀ a b, (left a b).2 ≤ B) (budgetR : ∀ a b, (right a b).2 ≤ B)
    (histories : List (HeightNode V h)) (simple : histories.Nodup) (complete : ∀ node, node ∈ histories)
    (roots : List V) :
    let out := pairedTemplateListWithWordWork left right histories roots
    out.1.toFinset = roots.toFinset.biUnion (fun r => joinHeightCopies r
      (inwardHeightTree G r h) (inwardHeightTree (reverseArcs G) r h)) ∧
     out.2 ≤ roots.length*(2*histories.length*((B+16)*h+34)+32)+3 := by
  induction roots with
  | nil => simp [pairedTemplateListWithWordWork]
  | cons root roots ih =>
    let rest := pairedTemplateListWithWordWork left right histories roots
    let L := inwardTemplateListWithWordWork left root histories
    let R := inwardTemplateListWithWordWork right root histories
    let rcopy := prependCopyArcsWithWordWork (outwardCopyArc root) rest.1 R.1
    let lcopy := prependCopyArcsWithWordWork (inwardCopyArc root) rcopy.1 L.1
    obtain ⟨tailResult,tailWork⟩ := ih
    obtain ⟨equalL,_,workL⟩ := inwardTemplateListWithWordWork_spec G left sameL B budgetL root histories simple complete
    obtain ⟨equalR,_,workR⟩ := inwardTemplateListWithWordWork_spec (reverseArcs G) right sameR B budgetR root histories simple complete
    obtain ⟨mappedR,tallyR⟩ := prependCopyArcsWithWordWork_spec (outwardCopyArc root) rest.1 R.1
    obtain ⟨mappedL,tallyL⟩ := prependCopyArcsWithWordWork_spec (inwardCopyArc root) rcopy.1 L.1
    change (heightForestRootLink root h::lcopy.1).toFinset = _ ∧
      rest.2+L.2+R.2+rcopy.2+lcopy.2+20 ≤ _
    constructor
    · change lcopy.1 = _ at mappedL
      change rcopy.1 = _ at mappedR
      change L.1.toFinset = _ at equalL
      change R.1.toFinset = _ at equalR
      change rest.1.toFinset = _ at tailResult
      rw [mappedL,mappedR,List.toFinset_cons,List.toFinset_append,List.toFinset_append,
        mapCopy_inward,mapCopy_outward,equalL,equalR,tailResult, List.toFinset_cons, Finset.biUnion_insert]
      unfold joinHeightCopies
      rw [← Finset.singleton_union]
      ac_rfl
    · have lenL : L.1.length ≤ histories.length := inwardTemplateListWithWordWork_length left root histories
      have lenR : R.1.length ≤ histories.length := inwardTemplateListWithWordWork_length right root histories
      change L.2 ≤ _ at workL
      change R.2 ≤ _ at workR
      change rest.2 ≤ _ at tailWork
      change lcopy.2 = _ at tallyL
      change rcopy.2 = _ at tallyR
      rw [List.length_cons, Nat.succ_mul, tallyL, tallyR]
      have perRoot : L.2+R.2+(12*R.1.length+3)+(12*L.1.length+3)+20 ≤
          2*histories.length*((B+16)*h+34)+32 := by
        calc
          _ ≤ 2*histories.length*((B+16)*h+22)+24*histories.length+32 := by rw [Nat.mul_assoc]; omega
          _ = _ := by ring
      omega

/-- The paired forest list has exactly the ordinary forest's arc set. -/
theorem pairedTemplateListWithWordWork_spec {h : ℕ} (G : Arcs V) (left right : V → V → Bool × ℕ)
    (sameL : ∀ a b, (left a b).1 = true ↔ Reach G b a)
    (sameR : ∀ a b, (right a b).1 = true ↔ Reach (reverseArcs G) b a)
    (B : ℕ) (budgetL : ∀ a b, (left a b).2 ≤ B) (budgetR : ∀ a b, (right a b).2 ≤ B)
    (histories : List (HeightNode V h)) (simple : histories.Nodup) (complete : ∀ node, node ∈ histories)
    (roots : List V) (allRoots : ∀ r, r ∈ roots) :
    let out := pairedTemplateListWithWordWork left right histories roots
    out.1.toFinset = heightForest G h ∧ out.2 ≤ roots.length*(2*histories.length*((B+16)*h+34)+32)+3 := by
  have rootsEq : roots.toFinset = univ := Finset.eq_univ_of_forall (fun r => List.mem_toFinset.mpr (allRoots r))
  obtain ⟨equal,work⟩ := pairedTemplateListWithWordWork_partial G left right sameL sameR B budgetL budgetR
    histories simple complete roots
  rw [rootsEq] at equal
  exact ⟨equal,work⟩

private theorem pairedTemplateListWithWordWork_support {h : ℕ} (G : Arcs V)
    (left right : V → V → Bool × ℕ)
    (sameL : ∀ a b, (left a b).1 = true ↔ Reach G b a)
    (sameR : ∀ a b, (right a b).1 = true ↔ Reach (reverseArcs G) b a)
    (B : ℕ) (budgetL : ∀ a b, (left a b).2 ≤ B) (budgetR : ∀ a b, (right a b).2 ≤ B)
    (histories : List (HeightNode V h)) (simple : histories.Nodup) (complete : ∀ node, node ∈ histories)
    (roots : List V) (rootSimple : roots.Nodup) :
    let out := (pairedTemplateListWithWordWork left right histories roots).1
    (∀ e ∈ out, heightForestRoot e.1 ∈ roots) ∧ out.Nodup := by
  induction roots with
  | nil => simp [pairedTemplateListWithWordWork]
  | cons root roots ih =>
    let rest := pairedTemplateListWithWordWork left right histories roots
    let L := inwardTemplateListWithWordWork left root histories
    let R := inwardTemplateListWithWordWork right root histories
    let rightRows := R.1.map (outwardCopyArc root)
    let leftRows := L.1.map (inwardCopyArc root)
    let link := heightForestRootLink root h
    obtain ⟨rootNew,rootTail⟩ := List.nodup_cons.mp rootSimple
    obtain ⟨support,tailSimple⟩ := ih rootTail
    obtain ⟨_,leftSimple,_⟩ := inwardTemplateListWithWordWork_spec G left sameL B budgetL root histories simple complete
    obtain ⟨_,rightSimple,_⟩ := inwardTemplateListWithWordWork_spec (reverseArcs G) right sameR B budgetR root histories simple complete
    obtain ⟨addedR,_⟩ := prependCopyArcsWithWordWork_spec (outwardCopyArc root) rest.1 R.1
    obtain ⟨addedL,_⟩ := prependCopyArcsWithWordWork_spec (inwardCopyArc root)
      (prependCopyArcsWithWordWork (outwardCopyArc root) rest.1 R.1).1 L.1
    have leftTags (e) (on : e ∈ leftRows) :
        heightForestRoot e.1 = root ∧ heightForestSide e.1 = false ∧ heightForestSide e.2 = false := by
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp on
      simp [inwardCopyArc]
    have rightTags (e) (on : e ∈ rightRows) : heightForestRoot e.1 = root ∧ heightForestSide e.1 = true := by
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp on
      simp [outwardCopyArc]
    have leftInject : Function.Injective (inwardCopyArc (h := h) root) :=
      ((heightCopy root false).prodMap (heightCopy root false)).injective
    have rightInject : Function.Injective (outwardCopyArc (h := h) root) := by
      intro x y eq
      have same : x.swap = y.swap := ((heightCopy root true).prodMap (heightCopy root true)).injective eq
      exact congrArg Prod.swap same
    dsimp only
    rw [pairedTemplateListWithWordWork]
    dsimp only
    rw [addedL,addedR]
    change (∀ e ∈ link::(leftRows ++ (rightRows ++ rest.1)), heightForestRoot e.1 ∈ root::roots) ∧
      (link::(leftRows ++ (rightRows ++ rest.1))).Nodup
    constructor
    · intro e member
      rcases List.mem_cons.mp member with rfl | tail
      · exact List.mem_cons_self
      rcases List.mem_append.mp tail with v | more
      · exact List.mem_cons.mpr (Or.inl (leftTags e v).1)
      rcases List.mem_append.mp more with v | v
      · exact List.mem_cons.mpr (Or.inl (rightTags e v).1)
      · exact List.mem_cons_of_mem _ (support e v)
    · apply List.nodup_cons.mpr
      refine ⟨?_,List.nodup_append.mpr ⟨leftSimple.map leftInject, ?_,?_⟩⟩
      · intro member
        rcases List.mem_append.mp member with on | on
        · have impossible := (leftTags link on).2.2
          simp [link,heightForestRootLink] at impossible
        rcases List.mem_append.mp on with r | r
        · have impossible := (rightTags link r).2
          simp [link,heightForestRootLink] at impossible
        · exact rootNew (support link r)
      · refine List.nodup_append.mpr ⟨rightSimple.map rightInject,tailSimple,?_⟩
        intro a ar b br eq
        exact rootNew ((rightTags a ar).1 ▸ eq.symm ▸ support b br)
      · intro a al b bl eq
        rcases List.mem_append.mp bl with r | r
        · have aside := (leftTags a al).2.1
          have bside := (rightTags b r).2
          rw [eq,bside] at aside
          contradiction
        · exact rootNew ((leftTags a al).1 ▸ eq.symm ▸ support b r)

/-- Generate every bounded history once for the paired forest. -/
def pairedTemplateEnumeratedWithWordWork (n h : ℕ) (label : Fin n → V × ℕ)
    (left right : V → V → Bool × ℕ) (roots : List V) :=
  let histories := heightNodesWithWordWork n h label
  let forest := pairedTemplateListWithWordWork left right histories.1 roots
  (forest.1,histories.2+forest.2+6)

/-- The exact forest arc list and its work bound, including the one shared history enumeration. -/
theorem pairedTemplateEnumeratedWithWordWork_spec {n : ℕ} (vertices : V ≃ Fin n)
    (label : Fin n → V × ℕ) (C : ℕ) (sameLabel : ∀ i, (label i).1 = vertices.symm i)
    (labelBudget : ∀ i, (label i).2 ≤ C) (G : Arcs V) (left right : V → V → Bool × ℕ)
    (sameL : ∀ a b, (left a b).1 = true ↔ Reach G b a)
    (sameR : ∀ a b, (right a b).1 = true ↔ Reach (reverseArcs G) b a)
    (B : ℕ) (budgetL : ∀ a b, (left a b).2 ≤ B) (budgetR : ∀ a b, (right a b).2 ≤ B)
    (roots : List V) (allRoots : ∀ r, r ∈ roots) (rootSimple : roots.Nodup) (h : ℕ) :
    let H := heightLexBlockCount n h
    let out := pairedTemplateEnumeratedWithWordWork n h label left right roots
    out.1.toFinset = heightForest G h ∧ out.1.Nodup ∧
      out.2 ≤ (heightNodeIndexWordBudget h C+9)*H+roots.length*(2*H*((B+16)*h+34)+32)+5*h+16 := by
  let histories := heightNodesWithWordWork n h label
  let forest := pairedTemplateListWithWordWork left right histories.1 roots
  obtain ⟨complete,simple,_,len,enumeration⟩ := heightNodesWithWordWork_spec vertices label C sameLabel labelBudget h
  obtain ⟨agreesForest,work⟩ := pairedTemplateListWithWordWork_spec G left right sameL sameR B budgetL budgetR
    histories.1 simple complete roots allRoots
  have distinct := (pairedTemplateListWithWordWork_support G left right sameL sameR B budgetL budgetR
    histories.1 simple complete roots rootSimple).2
  refine ⟨agreesForest,distinct,?_⟩
  change histories.1.length = heightLexBlockCount n h at len
  change forest.2 ≤ roots.length*(2*histories.1.length*((B+16)*h+34)+32)+3 at work
  rw [len] at work
  change histories.2+forest.2+6 ≤ _
  change histories.2 ≤ _ at enumeration
  omega

end OnlineReachabilityPreservers
