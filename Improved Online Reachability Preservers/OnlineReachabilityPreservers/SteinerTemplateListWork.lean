import OnlineReachabilityPreservers.SteinerTemplateWork

/-! Meter construction of the inward template in a supplied complete history list. -/

namespace OnlineReachabilityPreservers

open Finset

private def templateChainWithWordWork {V : Type*} (step : V → V → Bool × ℕ) (root : V) :
    List V → Bool × ℕ
  | [] => (true,3)
  | next::suffix =>
    let edge := step root next
    if edge.1 then
      let rest := templateChainWithWordWork step next suffix
      (rest.1,edge.2+rest.2+8)
    else (false,edge.2+8)

private theorem templateChainWithWordWork_spec {V : Type*} (step : V → V → Bool × ℕ)
    (r : V → V → Prop) (same : ∀ a b, (step a b).1 = true ↔ r a b)
    (B : ℕ) (budget : ∀ a b, (step a b).2 ≤ B) (root : V) (suffix : List V) :
    let result := templateChainWithWordWork step root suffix
    (result.1 = true ↔ (root::suffix).IsChain r) ∧ result.2 ≤ (B+8)*suffix.length+3 := by
  induction suffix generalizing root with
  | nil => simp [templateChainWithWordWork]
  | cons next rest ih =>
    obtain ⟨keeps,tally⟩ := ih next
    have fits := budget root next
    by_cases good : (step root next).1 = true
    · have relation := (same root next).mp good
      simp only [templateChainWithWordWork, good, ite_true, List.isChain_cons_cons, relation, true_and]
      refine ⟨keeps,?_⟩
      rw [List.length_cons, Nat.mul_succ]
      omega
    · have relation := (not_congr (same root next)).mp good
      simp only [templateChainWithWordWork, good, ite_false, List.isChain_cons_cons, relation, false_and,
        Bool.false_eq_true, iff_self, true_and]
      rw [List.length_cons, Nat.mul_succ]
      omega

private def dropLastWithWordWork {A : Type*} : List A → List A × ℕ
  | [] => ([],3)
  | [_] => ([],5)
  | head::next::rest =>
    let suffix := dropLastWithWordWork (next::rest)
    (head::suffix.1,suffix.2+8)

private theorem dropLastWithWordWork_spec {A : Type*} (values : List A) :
    let out := dropLastWithWordWork values
    out.1 = values.dropLast ∧ out.2 ≤ 8*values.length+3 := by
  induction values with
  | nil => simp [dropLastWithWordWork]
  | cons head tail ih =>
    cases tail with
    | nil => simp [dropLastWithWordWork]
    | cons next rest =>
      obtain ⟨same,work⟩ := ih
      simp only [dropLastWithWordWork, List.dropLast_cons_cons, same, List.length_cons]
      exact ⟨trivial,by simp only [List.length_cons] at work; omega⟩

private def heightParentWithWordWork {V : Type*} {h : ℕ} (node : HeightNode V h) : HeightNode V h × ℕ :=
  let out := dropLastWithWordWork node.val
  have short : out.1.length ≤ h := by
    rw [(dropLastWithWordWork_spec node.val).1]
    exact (List.dropLast_prefix node.val).length_le.trans node.property
  (⟨out.1,short⟩,out.2+4)

private theorem heightParentWithWordWork_spec {V : Type*} {h : ℕ} (node : HeightNode V h) :
    let out := heightParentWithWordWork node
    out.1 = heightParent node ∧ out.2 ≤ 8*h+7 := by
  obtain ⟨same,tally⟩ := dropLastWithWordWork_spec node.val
  refine ⟨Subtype.ext same,?_⟩
  have short := node.property
  unfold heightParentWithWordWork
  dsimp only
  omega

/-- Scan each candidate history once. The result has at most one arc per history. -/
def inwardTemplateListWithWordWork {V : Type*} {h : ℕ} (step : V → V → Bool × ℕ) (root : V) :
    List (HeightNode V h) → List (HeightNode V h × HeightNode V h) × ℕ
  | [] => ([],3)
  | node::nodes =>
    let rest := inwardTemplateListWithWordWork step root nodes
    match node.val with
    | [] => (rest.1,rest.2+8)
    | _::_ =>
      let check := templateChainWithWordWork step root node.val
      if check.1 then
        let parent := heightParentWithWordWork node
        ((node,parent.1)::rest.1,rest.2+check.2+parent.2+12)
      else (rest.1,rest.2+check.2+10)

variable {V : Type*} [LinearOrder V] [Fintype V]

private theorem inwardTemplateListWithWordWork_members {h : ℕ} (G : Arcs V) (step : V → V → Bool × ℕ)
    (same : ∀ a b, (step a b).1 = true ↔ Reach G b a) (B : ℕ) (budget : ∀ a b, (step a b).2 ≤ B)
    (root : V) (nodes : List (HeightNode V h)) (simple : nodes.Nodup) :
    let out := inwardTemplateListWithWordWork step root nodes
    (∀ e, e ∈ out.1 ↔ ∃ u ∈ nodes, u.val ≠ [] ∧ heightHistoryValid G root u ∧ e = (u,heightParent u)) ∧
      out.1.Nodup ∧ out.2 ≤ nodes.length*((B+16)*h+22)+3 := by
  induction nodes with
  | nil => simp [inwardTemplateListWithWordWork]
  | cons node nodes ih =>
    let rest := inwardTemplateListWithWordWork step root nodes
    obtain ⟨free,tailSimple⟩ := List.nodup_cons.mp simple
    obtain ⟨members,nodup,work⟩ := ih tailSimple
    change rest.2 ≤ nodes.length*((B+16)*h+22)+3 at work
    let check := templateChainWithWordWork step root node.val
    have info := templateChainWithWordWork_spec step (fun a b => b ∈ reaches G a)
      (fun a b => (same a b).trans mem_reaches.symm) B budget root node.val
    have accept : check.1 = true ↔ heightHistoryValid G root node := info.1
    have count : check.2 ≤ (B+8)*h+3 :=
      info.2.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ node.property) _)
    have notInRest : (node,heightParent node) ∉ rest.1 := by
      intro seen
      obtain ⟨u,mem,_,_,eq⟩ := (members _).mp seen
      have equal : node = u := congrArg Prod.fst eq
      exact free (equal ▸ mem)
    cases shape : node.val with
    | nil =>
      simp only [inwardTemplateListWithWordWork, shape]
      refine ⟨?_,nodup,?_⟩
      · intro e
        rw [members]
        constructor
        · rintro ⟨u,mem,legal⟩
          exact ⟨u,List.mem_cons_of_mem _ mem,legal⟩
        · rintro ⟨u,mem,nonempty,legal⟩
          rcases List.mem_cons.mp mem with eq | tail
          · exact (nonempty (eq.symm ▸ shape)).elim
          · exact ⟨u,tail,nonempty,legal⟩
      · change rest.2+8 ≤ _
        rw [List.length_cons, Nat.succ_mul]
        omega
    | cons v suffix =>
      have nonempty : node.val ≠ [] := by simp [shape]
      let checked := templateChainWithWordWork step root (v::suffix)
      have checkEq : checked = check := by
        dsimp only [checked,check]
        rw [shape]
      have allowed : checked.1 = true ↔ heightHistoryValid G root node := checkEq.symm ▸ accept
      have bounded : checked.2 ≤ (B+8)*h+3 := checkEq.symm ▸ count
      by_cases good : (templateChainWithWordWork step root (v::suffix)).1 = true
      · have valid := allowed.mp good
        obtain ⟨parentEq,parentWork⟩ := heightParentWithWordWork_spec node
        simp only [inwardTemplateListWithWordWork, shape, ite_eq_left good, parentEq]
        refine ⟨?_, List.nodup_cons.mpr ⟨notInRest,nodup⟩,?_⟩
        · intro e
          rw [List.mem_cons, members]
          constructor
          · rintro (equal | ⟨u,mem,legal⟩)
            · exact ⟨node,List.mem_cons_self,nonempty,valid,equal⟩
            · exact ⟨u,List.mem_cons_of_mem _ mem,legal⟩
          · rintro ⟨u,mem,good⟩
            rcases List.mem_cons.mp mem with rfl | tail
            · exact Or.inl good.2.2
            · exact Or.inr ⟨u,tail,good⟩
        · let parent := heightParentWithWordWork node
          change parent.2 ≤ _ at parentWork
          change rest.2+checked.2+parent.2+12 ≤ _
          rw [List.length_cons, Nat.succ_mul]
          have costs : checked.2+parent.2+12 ≤ (B+16)*h+22 := by
            calc
              _ ≤ ((B+8)*h+3)+(8*h+7)+12 := by omega
              _ = _ := by ring
          omega
      · have rejected := (not_congr allowed).mp good
        simp only [inwardTemplateListWithWordWork, shape, ite_eq_right good]
        refine ⟨?_,nodup,?_⟩
        · intro e
          rw [members]
          constructor
          · rintro ⟨u,mem,legal⟩
            exact ⟨u,List.mem_cons_of_mem _ mem,legal⟩
          · rintro ⟨u,mem,legal⟩
            rcases List.mem_cons.mp mem with rfl | tail
            · exact (rejected legal.2.1).elim
            · exact ⟨u,tail,legal⟩
        · change rest.2+checked.2+10 ≤ _
          rw [List.length_cons, Nat.succ_mul]
          have compare : (B+8)*h ≤ (B+16)*h := Nat.mul_le_mul_right _ (by omega)
          omega

/-- The list-backed evaluator gives the exact inward height tree and returns
unique arcs, charging the validity scan, parent construction, and list work. -/
theorem inwardTemplateListWithWordWork_spec {h : ℕ} (G : Arcs V) (step : V → V → Bool × ℕ)
    (same : ∀ a b, (step a b).1 = true ↔ Reach G b a) (B : ℕ) (budget : ∀ a b, (step a b).2 ≤ B)
    (root : V) (nodes : List (HeightNode V h)) (simple : nodes.Nodup)
    (complete : ∀ node, node ∈ nodes) :
    let out := inwardTemplateListWithWordWork step root nodes
    out.1.toFinset = inwardHeightTree G root h ∧ out.1.Nodup ∧
      out.2 ≤ nodes.length*((B+16)*h+22)+3 := by
  obtain ⟨members,nodup,work⟩ := inwardTemplateListWithWordWork_members G step same B budget root nodes simple
  refine ⟨?_,nodup,work⟩
  ext ⟨u,v⟩
  change (u,v) ∈ _ ↔ Edge (inwardHeightTree G root h) u v
  rw [List.mem_toFinset,members, inwardHeightTree_edge_iff]
  constructor
  · rintro ⟨w,_,nonempty,valid,eq⟩
    cases eq
    exact ⟨nonempty,valid,rfl⟩
  · rintro ⟨nonempty,valid,rfl⟩
    exact ⟨u,complete u,nonempty,valid,rfl⟩

end OnlineReachabilityPreservers
