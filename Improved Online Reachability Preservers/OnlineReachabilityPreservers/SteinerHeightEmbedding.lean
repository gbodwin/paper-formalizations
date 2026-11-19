import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import OnlineReachabilityPreservers.SteinerHeightTree

/-! Embed the shortened rooted routes in the fixed metric template. -/

namespace OnlineReachabilityPreservers

open Finset

private theorem walk_split_append {V : Type*} {T : Arcs V} {s t : V} {left right : List (V × V)}
    (whole : Walk T s t (left ++ right)) :
    ∃ middle, Walk T s middle left ∧ Walk T middle t right := by
  induction left generalizing s with
  | nil => exact ⟨s, .nil s, whole⟩
  | cons e rest ih =>
    cases whole with
    | cons edge walk =>
      obtain ⟨middle, before, after⟩ := ih walk
      exact ⟨middle, .cons edge before, after⟩

private def arcListStart {V : Type*} (root : V) (arcs : List (V × V)) : V :=
  (arcs.head?.map Prod.fst).getD root

private theorem walk_start_eq {V : Type*} {T : Arcs V} {s t : V} {p : List (V × V)}
    (walk : Walk T s t p) : s = arcListStart t p := by
  cases walk <;> rfl

/-- The endpoint of an original root-first arc prefix. -/
def heightPrefixVertex {V : Type*} (root : V) (arcs : List (V ×ₗ V)) : V :=
  arcListStart root (arcs.map ofLex).reverse

private theorem walk_heightPrefix {V : Type*} {T : Arcs V} {s root : V} {path stem : List (V ×ₗ V)}
    (whole : Walk T s root (path.map ofLex).reverse) (initial : stem <+: path) :
    Walk T (heightPrefixVertex root stem) root (stem.map ofLex).reverse := by
  obtain ⟨rest, eq⟩ := initial
  rw [← eq, List.map_append, List.reverse_append] at whole
  obtain ⟨mid, _, tail⟩ := walk_split_append whole
  have start : mid = heightPrefixVertex root stem := walk_start_eq tail
  exact start ▸ tail

private theorem walk_heightSegment {V : Type*} {T : Arcs V} {s root : V}
    {path parent child : List (V ×ₗ V)}
    (whole : Walk T s root (path.map ofLex).reverse) (nested : parent <+: child) (initial : child <+: path) :
    Walk T (heightPrefixVertex root child) (heightPrefixVertex root parent)
      ((child.drop parent.length).map ofLex).reverse := by
  let left := (child.drop parent.length).map ofLex |>.reverse
  let right := (parent.map ofLex).reverse
  have before : Walk T (heightPrefixVertex root child) root (left ++ right) := by
    rw [show left ++ right = (child.map ofLex).reverse by
      dsimp [left, right]
      rw [← List.reverse_append, ← List.map_append, ← List.prefix_append_drop nested]]
    exact walk_heightPrefix whole initial
  obtain ⟨mid, segment, tail⟩ := walk_split_append before
  have start : mid = heightPrefixVertex root parent := walk_start_eq tail
  exact start ▸ segment

variable {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}

/-- The vertex sequence used to represent a block at a fixed depth. -/
def heightBlockHistory (paths : Fin n → List (V ×ₗ V)) (root : V) (branch height : ℕ) :
    ℕ → ℕ → List V
  | 0, _ => []
  | depth + 1, index =>
    heightBlockHistory paths root branch height depth (index / branch) ++
      [heightPrefixVertex root (heightBlockPath paths branch height (height - (depth + 1)) index)]

omit [Fintype V] in
theorem heightBlockHistory_length (paths : Fin n → List (V ×ₗ V)) (root : V)
    (branch height depth index : ℕ) :
    (heightBlockHistory paths root branch height depth index).length = depth := by
  induction depth generalizing index with
  | zero => rfl
  | succ depth ih => simp [heightBlockHistory, ih]

def heightBlockNode (paths : Fin n → List (V ×ₗ V)) (root : V) (branch height : ℕ)
    (depth index : ℕ) (bound : depth ≤ height) : HeightNode V height :=
  ⟨heightBlockHistory paths root branch height depth index,
    (heightBlockHistory_length paths root branch height depth index).trans_le bound⟩

omit [Fintype V] in
theorem heightBlockNode_label (paths : Fin n → List (V ×ₗ V)) (root : V) (branch height depth index : ℕ)
    (bound : depth ≤ height) :
    heightLabel root (heightBlockNode paths root branch height depth index bound) =
      heightPrefixVertex root (heightBlockPath paths branch height (height - depth) index) := by
  cases depth with
  | zero => simp [heightBlockNode, heightBlockHistory, heightLabel, heightBlockPath, heightPrefixVertex, arcListStart]
  | succ depth =>
    exact heightLabel_append root (heightBlockHistory paths root branch height depth (index / branch))
      (heightPrefixVertex root (heightBlockPath paths branch height (height - (depth + 1)) index)) _

private theorem heightBlockParent_active {branch height depth index : ℕ}
    (bound : depth + 1 ≤ height)
    (active : (terminalBlock n (branch ^ (height - (depth + 1))) index).Nonempty) :
    (terminalBlock n (branch ^ (height - depth)) (index / branch)).Nonempty := by
  have step : height - depth = height - (depth + 1) + 1 := by omega
  rw [step, pow_succ]
  exact active.mono (terminalBlock_subset_parent _ _ _ _)

omit [Fintype V] in
private theorem heightBlock_orig_walk {G : Arcs V} {root : V}
    {paths : Fin n → List (V ×ₗ V)} {ends : Fin n → V}
    (all : ∀ i, Walk G (ends i) root ((paths i).map ofLex).reverse)
    {branch height depth index : ℕ} (bound : depth + 1 ≤ height)
    (active : (terminalBlock n (branch ^ (height - (depth + 1))) index).Nonempty) :
    let level := height - (depth + 1)
    Walk G (heightPrefixVertex root (heightBlockPath paths branch height level index))
      (heightPrefixVertex root (heightBlockPath paths branch height (height - depth) (index / branch)))
      ((heightBlockSegment paths branch height level index).map ofLex).reverse := by
  let level := height - (depth + 1)
  have step : height - depth = level + 1 := by dsimp [level]; omega
  have low : level < height := by dsimp [level]; omega
  obtain ⟨i, inBlock⟩ := active
  have nested := heightBlockPath_parent_prefix paths low ⟨i, inBlock⟩
  have initial : heightBlockPath paths branch height level index <+: paths i := by
    simpa [heightBlockPath, low.ne] using terminalBlockPath_prefix paths inBlock
  rw [step]
  exact walk_heightSegment (all i) nested initial

theorem heightBlockNode_valid {G : Arcs V} {root : V}
    {paths : Fin n → List (V ×ₗ V)} {ends : Fin n → V}
    (all : ∀ i, Walk G (ends i) root ((paths i).map ofLex).reverse)
    {branch height depth index : ℕ} (bound : depth ≤ height)
    (active : (terminalBlock n (branch ^ (height - depth)) index).Nonempty) :
    heightHistoryValid G root (heightBlockNode paths root branch height depth index bound) := by
  induction depth generalizing index with
  | zero => simp [heightHistoryValid, heightBlockNode, heightBlockHistory]
  | succ depth ih =>
    let p := heightBlockNode paths root branch height depth (index / branch) (by omega)
    have previous : heightHistoryValid G root p := ih (by omega) (heightBlockParent_active bound active)
    have w := heightBlock_orig_walk all bound active
    have reach : Reach G (heightPrefixVertex root
        (heightBlockPath paths branch height (height - (depth + 1)) index)) (heightLabel root p) := by
      rw [heightBlockNode_label]
      exact w.reachable
    exact (heightHistoryValid_append _).mpr ⟨previous, reach⟩

theorem heightBlockNode_edge {G : Arcs V} {root : V}
    {paths : Fin n → List (V ×ₗ V)} {ends : Fin n → V}
    (all : ∀ i, Walk G (ends i) root ((paths i).map ofLex).reverse)
    {branch height depth index : ℕ} (bound : depth + 1 ≤ height)
    (active : (terminalBlock n (branch ^ (height - (depth + 1))) index).Nonempty) :
    Edge (inwardHeightTree G root height)
      (heightBlockNode paths root branch height (depth + 1) index bound)
      (heightBlockNode paths root branch height depth (index / branch) (by omega)) := by
  have previous := heightBlockNode_valid all (by omega : depth ≤ height) (heightBlockParent_active bound active)
  have w := heightBlock_orig_walk all bound active
  apply inwardHeightTree_append _ previous
  rw [heightBlockNode_label]
  exact w.reachable

private def heightEmbeddingLink (paths : Fin n → List (V ×ₗ V)) (root : V) (branch height : ℕ)
    (level : Fin height) (index : ℕ) : HeightNode V height × HeightNode V height :=
  let depth := height - (level.val + 1)
  (heightBlockNode paths root branch height (depth + 1) index (by dsimp [depth]; omega),
    heightBlockNode paths root branch height depth (index / branch) (Nat.sub_le _ _))

/-- The metric links selected by the shortened routes of one original tree. -/
def heightEmbeddingLinks (paths : Fin n → List (V ×ₗ V)) (root : V) (branch height : ℕ) :
    Arcs (HeightNode V height) :=
  (univ : Finset (Fin height)).biUnion fun level =>
    (activeTerminalBlocks n (branch ^ level.val)).image (heightEmbeddingLink paths root branch height level)

omit [Fintype V] in
private theorem heightEmbeddingLink_mem {paths : Fin n → List (V ×ₗ V)}
    (root : V) (branch height : ℕ) (level : Fin height) {j : ℕ}
    (active : j ∈ activeTerminalBlocks n (branch ^ level.val)) :
    heightEmbeddingLink paths root branch height level j ∈ heightEmbeddingLinks paths root branch height :=
  mem_biUnion.mpr ⟨level, mem_univ _, mem_image_of_mem _ active⟩

theorem heightEmbeddingLinks_sub {G : Arcs V} {root : V}
    {paths : Fin n → List (V ×ₗ V)} {ends : Fin n → V}
    (all : ∀ i, Walk G (ends i) root ((paths i).map ofLex).reverse) (branch height : ℕ) :
    heightEmbeddingLinks paths root branch height ⊆ inwardHeightTree G root height := by
  intro e he
  obtain ⟨level, _, inLevel⟩ := mem_biUnion.mp he
  obtain ⟨j, active, rfl⟩ := mem_image.mp inLevel
  let depth := height - (level.val + 1)
  have depthBound : depth + 1 ≤ height := by dsimp [depth]; omega
  have atLevel : height - (depth + 1) = level.val := by dsimp [depth]; omega
  have present := (mem_filter.mp active).2
  change (terminalBlock n (branch ^ level.val) j).Nonempty at present
  rw [← atLevel] at present
  exact heightBlockNode_edge all depthBound present

omit [Fintype V] in
private theorem heightBlockNode_reach {paths : Fin n → List (V ×ₗ V)}
    (root : V) (branch height : ℕ) (i : Fin n) {depth : ℕ} (bound : depth ≤ height) :
    Reach (heightEmbeddingLinks paths root branch height)
      (heightBlockNode paths root branch height depth (i.val / branch ^ (height - depth)) bound) heightRoot := by
  induction depth with
  | zero => exact .refl
  | succ depth ih =>
    let level := height - (depth + 1)
    let l : Fin height := ⟨level, by dsimp [level]; omega⟩
    let j := i.val / branch ^ level
    have active : j ∈ activeTerminalBlocks n (branch ^ level) :=
      mem_filter.mpr ⟨mem_range.mpr ((Nat.div_le_self _ _).trans_lt i.isLt), ⟨i, mem_terminalBlock.mpr rfl⟩⟩
    have depthEq : height - (l.val + 1) = depth := by dsimp [l, level]; omega
    have prevEq : j / branch = i.val / branch ^ (height - depth) := by
      have next : height - depth = level + 1 := by dsimp [level]; omega
      rw [next, pow_succ, ← Nat.div_div_eq_div_mul]
    have edge := heightEmbeddingLink_mem (paths := paths) root branch height l active
    simp only [heightEmbeddingLink, depthEq, prevEq] at edge
    exact (ih (by omega)).head edge

omit [Fintype V] in
theorem heightEmbeddingLinks_terminal {G : Arcs V} {root : V}
    {paths : Fin n → List (V ×ₗ V)} {ends : Fin n → V}
    (all : ∀ i, Walk G (ends i) root ((paths i).map ofLex).reverse)
    (branch height : ℕ) (positive : 0 < height) (i : Fin n) :
    ∃ a : HeightNode V height, a.val.length = height ∧ heightLabel root a = ends i ∧
      Reach (heightEmbeddingLinks paths root branch height) a heightRoot := by
  let a := heightBlockNode paths root branch height height (i.val / branch ^ (height - height)) le_rfl
  refine ⟨a, heightBlockHistory_length _ _ _ _ _ _, ?_, heightBlockNode_reach root branch height i le_rfl⟩
  have start : heightPrefixVertex root (paths i) = ends i := (walk_start_eq (all i)).symm
  rw [heightBlockNode_label]
  simpa [heightBlockPath, positive.ne, terminalBlockPath_singleton] using start

private theorem heightEmbeddingLink_weight_le {G : Arcs V} {root : V}
    {paths : Fin n → List (V ×ₗ V)} {ends : Fin n → V}
    (all : ∀ i, Walk G (ends i) root ((paths i).map ofLex).reverse)
    (nodup : ∀ i, (paths i).Nodup) (branch height : ℕ) (l : Fin height)
    {j : ℕ} (active : j ∈ activeTerminalBlocks n (branch ^ l.val)) :
    heightLinkWeight G root (heightEmbeddingLink paths root branch height l j) ≤
      (heightBlockSegment paths branch height l.val j).toFinset.card := by
  let depth := height - (l.val + 1)
  have depthBound : depth + 1 ≤ height := by dsimp [depth]; omega
  have atLevel : height - (depth + 1) = l.val := by dsimp [depth]; omega
  have present := (mem_filter.mp active).2
  change (terminalBlock n (branch ^ l.val) j).Nonempty at present
  have representative : (terminalBlock n (branch ^ (height - (depth + 1))) j).Nonempty := by
    rw [atLevel]
    exact present
  have w := heightBlock_orig_walk all depthBound representative
  obtain ⟨i, inBlock⟩ := present
  have prefixPath : heightBlockPath paths branch height l.val j <+: paths i := by
    simpa [heightBlockPath, l.isLt.ne] using terminalBlockPath_prefix paths inBlock
  have segmentNodup : (heightBlockSegment paths branch height l.val j).Nodup :=
    (List.drop_sublist _ _).nodup (prefixPath.nodup (nodup i))
  rw [List.toFinset_card_of_nodup segmentNodup]
  simp only [heightLinkWeight, heightEmbeddingLink, heightBlockNode_label]
  change hops G (heightPrefixVertex root (heightBlockPath paths branch height (height - (depth + 1)) j))
    (heightPrefixVertex root (heightBlockPath paths branch height (height - depth) (j / branch))) ≤ _
  have measured := hops_le_walk w
  simpa [atLevel] using measured

private theorem sum_image_weight_le {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (f : A → B) (w : B → ℕ) :
    (∑ b ∈ S.image f, w b) ≤ ∑ a ∈ S, w (f a) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S fresh ih =>
    rw [image_insert, sum_insert fresh]
    by_cases occurs : f a ∈ S.image f
    · rw [insert_eq_of_mem occurs]
      exact ih.trans (Nat.le_add_left _ _)
    · rw [sum_insert occurs]
      exact Nat.add_le_add_left ih _

theorem sum_biUnion_weight_le {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (f : A → Finset B) (w : B → ℕ) :
    (∑ b ∈ S.biUnion f, w b) ≤ ∑ a ∈ S, ∑ b ∈ f a, w b := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S fresh ih =>
    rw [biUnion_insert, sum_insert fresh]
    have bound : ∑ b ∈ f a ∪ S.biUnion f, w b ≤ (∑ b ∈ f a, w b) + ∑ b ∈ S.biUnion f, w b := by
      have split : f a ∪ S.biUnion f = f a ∪ (S.biUnion f \ f a) := by ext b; simp
      have disjoint : Disjoint (f a) (S.biUnion f \ f a) :=
        disjoint_left.mpr fun b hb hother => (mem_sdiff.mp hother).2 hb
      rw [split, sum_union disjoint]
      exact Nat.add_le_add_left (sum_le_sum_of_subset (sdiff_subset)) _
    exact bound.trans (Nat.add_le_add_left ih _)

/-- A rooted tree embeds into the fixed bounded-depth metric tree while
preserving its terminal labels and charging only the shortened links. -/
theorem rootedHeightEmbedding (G T : Arcs V) (root : V) (sub : T ⊆ G) (tree : InArborescence T root)
    (terminals : Finset V) (reachable : ∀ v ∈ terminals, Reach T v root) {branch height : ℕ}
    (branchPos : 0 < branch) (heightPos : 0 < height) (enough : terminals.card ≤ branch ^ height) :
    ∃ links : Arcs (HeightNode V height), links ⊆ inwardHeightTree G root height ∧
      (∀ v ∈ terminals, ∃ a : HeightNode V height, a.val.length = height ∧ heightLabel root a = v ∧
        Reach links a heightRoot) ∧
      (∑ link ∈ links, heightLinkWeight G root link) ≤ 2 * branch * height * T.card := by
  let xs := rootedTerminalOrder T root terminals
  let paths (i : Fin xs.length) := (ofLex (xs.get i)).1
  let ends (i : Fin xs.length) := (ofLex (xs.get i)).2
  have walks (i : Fin xs.length) : Walk G (ends i) root ((paths i).map ofLex).reverse :=
    (rootedTerminalOrder_walk reachable i).mono sub
  have nodup (i : Fin xs.length) : (paths i).Nodup := rootedTerminalOrder_nodup tree reachable i
  let links := heightEmbeddingLinks paths root branch height
  refine ⟨links, heightEmbeddingLinks_sub walks branch height, ?_, ?_⟩
  · intro v hv
    obtain ⟨i, eq⟩ := rootedTerminalOrder_covers hv (T := T) (root := root)
    obtain ⟨a, length, label, route⟩ := heightEmbeddingLinks_terminal walks branch height heightPos i
    exact ⟨a, length, label.trans eq, route⟩
  · have shortened := rootedHeightBlockSegments_weight_le tree reachable (fun _ => 1) branchPos enough
    change (∑ e ∈ (univ : Finset (Fin height)).biUnion (fun level =>
      (activeTerminalBlocks xs.length (branch ^ level.val)).image (heightEmbeddingLink paths root branch height level)),
        heightLinkWeight G root e) ≤ _
    calc
      _ ≤ ∑ level : Fin height, ∑ e ∈ (activeTerminalBlocks xs.length (branch ^ level.val)).image
          (heightEmbeddingLink paths root branch height level), heightLinkWeight G root e :=
        sum_biUnion_weight_le _ _ _
      _ ≤ ∑ level : Fin height, ∑ j ∈ activeTerminalBlocks xs.length (branch ^ level.val),
          (heightBlockSegment paths branch height level.val j).toFinset.card := by
        apply sum_le_sum
        intro l _
        refine (sum_image_weight_le _ _ _).trans (sum_le_sum fun j active => ?_)
        exact heightEmbeddingLink_weight_le walks nodup branch height l active
      _ = ∑ level ∈ range height, ∑ j ∈ activeTerminalBlocks xs.length (branch ^ level),
          (heightBlockSegment paths branch height level j).toFinset.card :=
        Fin.sum_univ_eq_sum_range
          (fun level => ∑ j ∈ activeTerminalBlocks xs.length (branch ^ level),
            (heightBlockSegment paths branch height level j).toFinset.card) height
      _ ≤ _ := by simpa [xs, paths] using shortened

/-- Branch count determined by an upper bound on the number of terminals. -/
def heightReductionBranch (height terminals : ℕ) : ℕ := Nat.nthRoot height terminals + 1

theorem heightReductionBranch_pow {height : ℕ} (heightPos : 0 < height) (terminals : ℕ) :
    terminals ≤ heightReductionBranch height terminals ^ height :=
  (Nat.lt_pow_nthRoot_add_one heightPos.ne' terminals).le

theorem heightReductionBranch_le {height terminals : ℕ} (heightPos : 0 < height)
    (terminalsPos : 0 < terminals) :
    (heightReductionBranch height terminals : ℝ) ≤ 2 * (terminals : ℝ) ^ (1 / (height : ℝ)) := by
  let value : ℝ := (terminals : ℝ) ^ (1 / (height : ℝ))
  have heightR : (height : ℝ) ≠ 0 := (Nat.cast_pos.mpr heightPos).ne'
  have power : value ^ height = terminals := by
    dsimp [value]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    rw [div_mul_cancel₀ _ heightR, Real.rpow_one]
  have base : (Nat.nthRoot height terminals : ℝ) ≤ value := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by dsimp [value]; positivity) heightPos.ne').mp
    rw [power]
    exact_mod_cast (Nat.pow_nthRoot_le_iff.mpr (Or.inl heightPos.ne') :
      Nat.nthRoot height terminals ^ height ≤ terminals)
  have terminalOne : (1 : ℝ) ≤ terminals := by exact_mod_cast terminalsPos
  have v1 : 1 ≤ value := Real.one_le_rpow terminalOne (by positivity)
  push_cast [heightReductionBranch]
  change (Nat.nthRoot height terminals : ℝ) + 1 ≤ 2 * value
  linarith only [base, v1]

/-- The unweighted forward height-reduction bound with one uniform constant.
The fixed template depends on the original graph, root and depth. -/
theorem rootedHeightEmbedding_bounded (G T : Arcs V) (root : V) (sub : T ⊆ G)
    (tree : InArborescence T root) (terminals : Finset V) (reachable : ∀ v ∈ terminals, Reach T v root)
    {height k : ℕ} (heightPos : 0 < height) (kPos : 0 < k) (enough : terminals.card ≤ k) :
    ∃ links : Arcs (HeightNode V height), links ⊆ inwardHeightTree G root height ∧
      (∀ v ∈ terminals, ∃ a : HeightNode V height, a.val.length = height ∧ heightLabel root a = v ∧
        Reach links a heightRoot) ∧
      (∑ link ∈ links, (heightLinkWeight G root link : ℝ)) ≤
        4 * (height : ℝ) * (k : ℝ) ^ (1 / (height : ℝ)) * (T.card : ℝ) := by
  let branch := heightReductionBranch height k
  have branchPos : 0 < branch := Nat.succ_pos _
  obtain ⟨links, allowed, covered, cost⟩ :=
    rootedHeightEmbedding G T root sub tree terminals reachable branchPos heightPos
      (enough.trans (heightReductionBranch_pow heightPos k))
  refine ⟨links, allowed, covered, ?_⟩
  have liftCost : (∑ link ∈ links, (heightLinkWeight G root link : ℝ)) ≤
      2 * (branch : ℝ) * (height : ℝ) * (T.card : ℝ) := by exact_mod_cast cost
  calc
    _ ≤ 2 * (branch : ℝ) * (height : ℝ) * (T.card : ℝ) := liftCost
    _ ≤ 2 * (2 * (k : ℝ) ^ (1 / (height : ℝ))) * (height : ℝ) * (T.card : ℝ) := by
      gcongr
      exact heightReductionBranch_le heightPos kPos
    _ = _ := by ring

end OnlineReachabilityPreservers
