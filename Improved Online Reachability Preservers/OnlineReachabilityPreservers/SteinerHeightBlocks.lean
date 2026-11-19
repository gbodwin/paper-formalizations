import Mathlib.Data.Finset.Sort
import OnlineReachabilityPreservers.SteinerHeightIntervals
import OnlineReachabilityPreservers.SteinerRootOrder

/-! Common prefixes on the consecutive blocks of a terminal traversal. -/

namespace OnlineReachabilityPreservers

open Finset

section Prefixes

variable {A : Type*} [DecidableEq A]

/-- The longest common prefix of two lists. -/
def commonListPrefix : List A → List A → List A
  | a :: l, b :: r => if a = b then a :: commonListPrefix l r else []
  | _, _ => []

theorem prefix_commonListPrefix_iff (common left right : List A) :
    common <+: commonListPrefix left right ↔ common <+: left ∧ common <+: right := by
  induction left generalizing common right with
  | nil => cases common <;> cases right <;> simp [commonListPrefix]
  | cons a left ih =>
    cases right with
    | nil => cases common <;> simp [commonListPrefix]
    | cons b right =>
      cases common with
      | nil => simp
      | cons c common =>
        by_cases eq : a = b
        · subst b
          simp [commonListPrefix, List.cons_prefix_cons, ih, and_assoc, and_left_comm]
        · have notBoth : ¬ (c = a ∧ c = b) := fun h => eq (h.1.symm.trans h.2)
          constructor
          · intro no
            simp [commonListPrefix, eq] at no
          · intro both
            have ca := (List.cons_prefix_cons.mp both.1).1
            have cb := (List.cons_prefix_cons.mp both.2).1
            exact (notBoth ⟨ca, cb⟩).elim

private theorem prefix_commonListFold_iff {I : Type*} (paths : I → List A)
    (block : List I) (initial common : List A) :
    common <+: block.foldl (fun stem i => commonListPrefix stem (paths i)) initial ↔
      common <+: initial ∧ ∀ i ∈ block, common <+: paths i := by
  induction block generalizing initial with
  | nil => simp
  | cons i rest ih =>
    rw [List.foldl_cons, ih, prefix_commonListPrefix_iff]
    simp [and_assoc]

/-- The terminals in block `index`, with `width` consecutive positions per block. -/
def terminalBlock (n width index : ℕ) : Finset (Fin n) :=
  univ.filter fun i => i.val / width = index

theorem mem_terminalBlock {n width index : ℕ} {i : Fin n} :
    i ∈ terminalBlock n width index ↔ i.val / width = index := by
  simp [terminalBlock]

theorem terminalBlock_subset_parent (n width branch index : ℕ) :
    terminalBlock n width index ⊆ terminalBlock n (width * branch) (index / branch) := by
  intro i hi
  rw [mem_terminalBlock, ← Nat.div_div_eq_div_mul, mem_terminalBlock.mp hi]

variable {n : ℕ}

/-- The longest prefix shared by all routes in one nonempty block.
An empty block is represented by the empty list. -/
def terminalBlockPath (paths : Fin n → List A) (width index : ℕ) : List A :=
  match (terminalBlock n width index).sort (· ≤ ·) with
  | [] => []
  | i :: rest => rest.foldl (fun stem j => commonListPrefix stem (paths j)) (paths i)

theorem prefix_terminalBlockPath_iff (paths : Fin n → List A) {width index : ℕ}
    (active : (terminalBlock n width index).Nonempty) (common : List A) :
    common <+: terminalBlockPath paths width index ↔
      ∀ i ∈ terminalBlock n width index, common <+: paths i := by
  let s := terminalBlock n width index
  have length_pos : 0 < (s.sort (· ≤ ·)).length := by
    rw [Finset.length_sort]
    exact card_pos.mpr active
  change _ <+: (match s.sort (· ≤ ·) with
    | [] => []
    | i :: rest => rest.foldl (fun stem j => commonListPrefix stem (paths j)) (paths i)) ↔ _
  cases eq : s.sort (· ≤ ·) with
  | nil => simp [eq] at length_pos
  | cons i rest =>
    rw [prefix_commonListFold_iff]
    have equiv (j : Fin n) : j ∈ s ↔ j ∈ i :: rest := by
      rw [← eq, Finset.mem_sort]
    change _ ↔ ∀ j ∈ s, _
    simp only [equiv, List.forall_mem_cons]

theorem terminalBlockPath_prefix (paths : Fin n → List A) {width index : ℕ}
    {i : Fin n} (hi : i ∈ terminalBlock n width index) :
    terminalBlockPath paths width index <+: paths i :=
  (prefix_terminalBlockPath_iff paths ⟨i, hi⟩ _).mp List.prefix_rfl i hi

theorem terminalBlockPath_parent_prefix (paths : Fin n → List A) {width branch index : ℕ}
    (active : (terminalBlock n width index).Nonempty) :
    terminalBlockPath paths (width * branch) (index / branch) <+: terminalBlockPath paths width index :=
  (prefix_terminalBlockPath_iff paths active _).mpr fun _i hi =>
    terminalBlockPath_prefix paths (terminalBlock_subset_parent n width branch index hi)

theorem terminalBlockPath_singleton (paths : Fin n → List A) (i : Fin n) :
    terminalBlockPath paths 1 i.val = paths i := by
  have hi : i ∈ terminalBlock n 1 i.val := mem_terminalBlock.mpr (Nat.div_one _)
  apply (terminalBlockPath_prefix paths hi).eq_of_length_le
  have reverse : paths i <+: terminalBlockPath paths 1 i.val := by
    apply (prefix_terminalBlockPath_iff paths ⟨i, hi⟩ _).mpr
    intro j hj
    have eq : j = i := Fin.ext (by simpa using mem_terminalBlock.mp hj)
    simp [eq]
  exact reverse.length_le

/-- When occurrences of an arc correspond to one fixed prefix, the arc
occurs in a block prefix exactly when every route in that block uses it. -/
theorem terminalBlockPath_mem_iff (paths : Fin n → List A) {width index : ℕ}
    (active : (terminalBlock n width index).Nonempty) {e : A}
    (stem : List A) (onStem : e ∈ stem) (uses : ∀ i, e ∈ paths i ↔ stem <+: paths i) :
    e ∈ terminalBlockPath paths width index ↔
      ∀ i ∈ terminalBlock n width index, e ∈ paths i := by
  constructor
  · intro onBlock i hi
    exact (terminalBlockPath_prefix paths hi).subset onBlock
  · intro all
    have h := (prefix_terminalBlockPath_iff paths active stem).mpr
      (fun i hi => (uses i).mp (all i hi))
    exact h.subset onStem

/-- Candidate block indices that contain at least one terminal. -/
def activeTerminalBlocks (n width : ℕ) : Finset ℕ :=
  (range n).filter fun i => (terminalBlock n width i).Nonempty

/-- The root represents the empty prefix. Every lower block represents its
longest common prefix. -/
def heightBlockPath (paths : Fin n → List A) (branch height level index : ℕ) : List A :=
  if level = height then [] else terminalBlockPath paths (branch ^ level) index

/-- The original arcs added from a parent prefix to its child prefix.
They appear in root-to-terminal order. -/
def heightBlockSegment (paths : Fin n → List A) (branch height level index : ℕ) : List A :=
  (heightBlockPath paths branch height level index).drop
    (heightBlockPath paths branch height (level + 1) (index / branch)).length

theorem heightBlockPath_parent_prefix (paths : Fin n → List A) {branch height level index : ℕ}
    (level_lt : level < height) (active : (terminalBlock n (branch ^ level) index).Nonempty) :
    heightBlockPath paths branch height (level + 1) (index / branch) <+:
      heightBlockPath paths branch height level index := by
  by_cases atRoot : level + 1 = height
  · simp [heightBlockPath, atRoot]
  · simpa [heightBlockPath, level_lt.ne, atRoot, pow_succ] using terminalBlockPath_parent_prefix paths active

def heightBlockArcUses (paths : Fin n → List A) (branch height level : ℕ) (arc : A) : Finset ℕ :=
  (activeTerminalBlocks n (branch ^ level)).filter fun i => arc ∈ heightBlockSegment paths branch height level i

private theorem heightBlockArcUses_nonroot {paths : Fin n → List A} {branch height level : ℕ}
    (level_lt : level < height) (notTop : level + 1 ≠ height)
    (nodup : ∀ i, (paths i).Nodup) {e : A} {stem : List A} (onStem : e ∈ stem)
    (uses : ∀ i, e ∈ paths i ↔ stem <+: paths i) {first past : ℕ}
    (interval : ∀ i : Fin n, e ∈ paths i ↔ first ≤ i.val ∧ i.val < past) :
    heightBlockArcUses paths branch height level e ⊆
      terminalIntervalCrossings n (branch ^ level) branch first past := by
  classical
  intro index hindex
  obtain ⟨present, arcSegment⟩ := mem_filter.mp hindex
  obtain ⟨inRange, nonempty⟩ := mem_filter.mp present
  obtain ⟨child, hchild⟩ := nonempty
  let childPath := heightBlockPath paths branch height level index
  let parentPath := heightBlockPath paths branch height (level + 1) (index / branch)
  let segment := heightBlockSegment paths branch height level index
  have parent := heightBlockPath_parent_prefix paths level_lt ⟨child, hchild⟩
  have split : parentPath ++ segment = childPath := (List.prefix_append_drop parent).symm
  have childPref : childPath <+: paths child := by
    simpa [childPath, heightBlockPath, level_lt.ne] using terminalBlockPath_prefix paths hchild
  have childNoDup : childPath.Nodup := childPref.nodup (nodup child)
  have disjoint : parentPath.Disjoint segment := (List.nodup_append'.mp (split ▸ childNoDup)).2.2
  have childUse : e ∈ childPath := split ▸ List.mem_append_right parentPath arcSegment
  have parentAvoids : e ∉ parentPath := fun h => List.disjoint_left.mp disjoint h arcSegment
  have parentActive : (terminalBlock n (branch ^ level * branch) (index / branch)).Nonempty :=
    ⟨child, terminalBlock_subset_parent _ _ _ _ hchild⟩
  have parentDoesNotUse : e ∉ terminalBlockPath paths (branch ^ level * branch) (index / branch) := by
    simpa [parentPath, heightBlockPath, notTop, pow_succ] using parentAvoids
  have missing : ∃ other ∈ terminalBlock n (branch ^ level * branch) (index / branch), e ∉ paths other := by
    by_contra no
    push Not at no
    exact parentDoesNotUse ((terminalBlockPath_mem_iff paths parentActive stem onStem uses).mpr no)
  obtain ⟨other, hother, lacks⟩ := missing
  obtain ⟨afterFirst, beforePast⟩ := (interval child).mp (childPref.subset childUse)
  exact mem_filter.mpr ⟨inRange, child.val, mem_range.mpr child.isLt,
    mem_terminalBlock.mp hchild, afterFirst, beforePast, other.val, mem_range.mpr other.isLt,
    mem_terminalBlock.mp hother, fun value => lacks ((interval other).mpr value)⟩

/-- No original arc occurs in more than twice the branch count of the
compressed segments at a single level. -/
theorem heightBlockArcUses_card {paths : Fin n → List A} {branch height level : ℕ}
    (positive : 0 < branch) (enough : n ≤ branch ^ height) (level_lt : level < height)
    (nodup : ∀ i, (paths i).Nodup) {e : A} {stem : List A} (onStem : e ∈ stem)
    (uses : ∀ i, e ∈ paths i ↔ stem <+: paths i) {first past : ℕ}
    (interval : ∀ i : Fin n, e ∈ paths i ↔ first ≤ i.val ∧ i.val < past) :
    (heightBlockArcUses paths branch height level e).card ≤ 2 * branch := by
  by_cases top : level + 1 = height
  · have parentSize : n ≤ branch ^ level * branch := by
      rw [← top, pow_succ] at enough
      exact enough
    have sub : heightBlockArcUses paths branch height level e ⊆ range branch := by
      intro j hj
      obtain ⟨i, hi⟩ := (mem_filter.mp (mem_filter.mp hj).1).2
      have bound : i.val < branch * branch ^ level :=
        i.isLt.trans_le (parentSize.trans_eq (Nat.mul_comm _ _))
      exact mem_range.mpr (mem_terminalBlock.mp hi ▸ (Nat.div_lt_iff_lt_mul (pow_pos positive _)).mpr bound)
    calc
      _ ≤ (range branch).card := card_le_card sub
      _ ≤ _ := by simp; omega
  · exact (card_le_card (heightBlockArcUses_nonroot level_lt top nodup onStem uses interval)).trans
      (terminalIntervalCrossings_card _ _ _ _ _ positive)

theorem heightBlockArcUses_total {paths : Fin n → List A} {branch height : ℕ}
    (positive : 0 < branch) (enough : n ≤ branch ^ height)
    (nodup : ∀ i, (paths i).Nodup) {e : A} {stem : List A} (onStem : e ∈ stem)
    (uses : ∀ i, e ∈ paths i ↔ stem <+: paths i) {first past : ℕ}
    (interval : ∀ i : Fin n, e ∈ paths i ↔ first ≤ i.val ∧ i.val < past) :
    (∑ level ∈ range height, (heightBlockArcUses paths branch height level e).card) ≤ 2 * branch * height := by
  calc
    _ ≤ ∑ _level ∈ range height, (2 * branch) :=
      sum_le_sum fun _ h => heightBlockArcUses_card positive enough (mem_range.mp h) nodup onStem uses interval
    _ = _ := by simp [Nat.mul_comm]

/-- The compressed segments encountered from the root to one terminal. -/
def terminalSegments (paths : Fin n → List A) (branch height : ℕ) (i : Fin n) :
    ℕ → List (List A)
  | 0 => []
  | depth + 1 =>
    let level := height - (depth + 1)
    terminalSegments paths branch height i depth ++
      [heightBlockSegment paths branch height level (i.val / branch ^ level)]

theorem terminalSegments_length (paths : Fin n → List A) (branch height : ℕ) (i : Fin n) (depth : ℕ) :
    (terminalSegments paths branch height i depth).length = depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [terminalSegments, ih]

private theorem terminalSegments_flatten_prefix (paths : Fin n → List A) (branch height : ℕ)
    (i : Fin n) {depth : ℕ} (inHeight : depth ≤ height) :
    (terminalSegments paths branch height i depth).flatten =
      heightBlockPath paths branch height (height - depth) (i.val / branch ^ (height - depth)) := by
  induction depth with
  | zero => simp [terminalSegments, heightBlockPath]
  | succ depth ih =>
    let level := height - (depth + 1)
    have earlier : depth ≤ height := by omega
    have atLevel : level < height := by dsimp only [level]; omega
    have eq : height - depth = level + 1 := by dsimp only [level]; omega
    have active : (terminalBlock n (branch ^ level) (i.val / branch ^ level)).Nonempty :=
      ⟨i, mem_terminalBlock.mpr rfl⟩
    have parent : heightBlockPath paths branch height (level+1) ((i.val / branch^level) / branch) <+:
        heightBlockPath paths branch height level (i.val / branch^level) :=
      heightBlockPath_parent_prefix paths atLevel active
    rw [terminalSegments, List.flatten_append, ih earlier, eq, pow_succ, ← Nat.div_div_eq_div_mul]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, heightBlockSegment]
    exact (List.prefix_append_drop parent).symm

/-- The height-many segments concatenate to the entire original terminal route. -/
theorem terminalSegments_flatten (paths : Fin n → List A) (branch height : ℕ)
    (positive : 0 < height) (i : Fin n) :
    (terminalSegments paths branch height i height).flatten = paths i := by
  rw [terminalSegments_flatten_prefix paths branch height i le_rfl]
  simp [heightBlockPath, positive.ne, terminalBlockPath_singleton]

/-- Total segment weight after shortening an ordered family of rooted routes. -/
theorem heightBlockSegments_weight_le (paths : Fin n → List A) (arcs : Finset A) (weight : A → ℕ)
    {branch height : ℕ} (positive : 0 < branch) (enough : n ≤ branch ^ height)
    (nodup : ∀ i, (paths i).Nodup) (support : ∀ i e, e ∈ paths i → e ∈ arcs)
    (stems : ∀ e ∈ arcs, ∃ stem, e ∈ stem ∧ ∀ i, e ∈ paths i ↔ stem <+: paths i)
    (intervals : ∀ e ∈ arcs, ∃ first past : ℕ, ∀ i : Fin n, e ∈ paths i ↔ first ≤ i.val ∧ i.val < past) :
    (∑ level ∈ range height, ∑ j ∈ activeTerminalBlocks n (branch ^ level),
      ∑ e ∈ (heightBlockSegment paths branch height level j).toFinset, weight e) ≤
        (2 * branch * height) * ∑ e ∈ arcs, weight e := by
  classical
  have charged (level : ℕ) (hlevel : level ∈ range height) :
      (∑ j ∈ activeTerminalBlocks n (branch ^ level),
        ∑ e ∈ (heightBlockSegment paths branch height level j).toFinset, weight e) =
      ∑ e ∈ arcs, (heightBlockArcUses paths branch height level e).card * weight e := by
    have atBlock j (hj : j ∈ activeTerminalBlocks n (branch ^ level)) :
        (∑ e ∈ (heightBlockSegment paths branch height level j).toFinset, weight e) =
          ∑ e ∈ arcs, if e ∈ heightBlockSegment paths branch height level j then weight e else 0 := by
      obtain ⟨i, hi⟩ := (mem_filter.mp hj).2
      have sub : (heightBlockSegment paths branch height level j).toFinset ⊆ arcs := by
        intro e he
        have hc := List.mem_of_mem_drop (List.mem_toFinset.mp he)
        have hp : heightBlockPath paths branch height level j <+: paths i := by
          simpa [heightBlockPath, (mem_range.mp hlevel).ne] using terminalBlockPath_prefix paths hi
        exact support i e (hp.subset hc)
      rw [← sum_filter]
      congr 1
      ext e
      simp only [List.mem_toFinset, mem_filter]
      exact ⟨fun he => ⟨sub (List.mem_toFinset.mpr he), he⟩, And.right⟩
    rw [sum_congr rfl atBlock, sum_comm]
    apply sum_congr rfl
    intro e _
    rw [← sum_filter]
    simp [heightBlockArcUses, Nat.mul_comm]
  calc
    _ = ∑ level ∈ range height, ∑ e ∈ arcs, (heightBlockArcUses paths branch height level e).card * weight e :=
      sum_congr rfl charged
    _ = ∑ e ∈ arcs, (∑ level ∈ range height, (heightBlockArcUses paths branch height level e).card) * weight e := by
      rw [sum_comm]
      simp only [sum_mul]
    _ ≤ ∑ e ∈ arcs, (2 * branch * height) * weight e := by
      apply sum_le_sum
      intro e he
      obtain ⟨stem, onStem, uses⟩ := stems e he
      obtain ⟨first, past, interval⟩ := intervals e he
      exact Nat.mul_le_mul_right _ (heightBlockArcUses_total positive enough nodup onStem uses interval)
    _ = _ := (mul_sum ..).symm

end Prefixes

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Height reduction on the terminal routes of an actual rooted arborescence.
It charges metric links by the weights of their original arcs. -/
theorem rootedHeightBlockSegments_weight_le {T : Arcs V} {root : V} (tree : InArborescence T root)
    {terminals : Finset V} (allReach : ∀ v ∈ terminals, Reach T v root) (weight : V × V → ℕ)
    {branch height : ℕ} (positive : 0 < branch) (enough : terminals.card ≤ branch ^ height) :
    let order := rootedTerminalOrder T root terminals
    let paths (i : Fin order.length) := (ofLex (order.get i)).1
    (∑ level ∈ range height, ∑ j ∈ activeTerminalBlocks order.length (branch ^ level),
      ∑ e ∈ (heightBlockSegment paths branch height level j).toFinset, weight (ofLex e)) ≤
        (2 * branch * height) * ∑ e ∈ T, weight e := by
  let order := rootedTerminalOrder T root terminals
  let paths (i : Fin order.length) := (ofLex (order.get i)).1
  let arcs : Finset (V ×ₗ V) := T.image toLex
  have size : order.length ≤ branch ^ height := (rootedTerminalOrder_length T root terminals).trans_le enough
  have support (i : Fin order.length) (e : V ×ₗ V) (member : e ∈ paths i) : e ∈ arcs := by
    exact mem_image.mpr ⟨ofLex e, rootedTerminalOrder_arc_mem allReach i member, rfl⟩
  have stems (e : V ×ₗ V) (member : e ∈ arcs) :
      ∃ stem, e ∈ stem ∧ ∀ i, e ∈ paths i ↔ stem <+: paths i := by
    obtain ⟨arc, present, rfl⟩ := mem_image.mp member
    exact rootedTerminalOrder_arc_prefix tree allReach present
  have intervals (e : V ×ₗ V) (member : e ∈ arcs) :
      ∃ first past : ℕ, ∀ i : Fin order.length, e ∈ paths i ↔ first ≤ i.val ∧ i.val < past := by
    obtain ⟨arc, present, rfl⟩ := mem_image.mp member
    exact rootedTerminalOrder_arc_interval tree allReach present
  have weightBound := heightBlockSegments_weight_le paths arcs (fun e => weight (ofLex e)) positive size
    (rootedTerminalOrder_nodup tree allReach) support stems intervals
  have originalWeight : (∑ e ∈ arcs, weight (ofLex e)) = ∑ e ∈ T, weight e := by
    rw [sum_image (fun _ _ _ _ eq => toLex.injective eq)]
    rfl
  simpa only [originalWeight] using weightBound

end OnlineReachabilityPreservers
