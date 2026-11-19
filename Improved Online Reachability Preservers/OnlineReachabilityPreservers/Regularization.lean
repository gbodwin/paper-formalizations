import Mathlib.Data.Sigma.Order
import OnlineReachabilityPreservers.SplitPreservation

/-! Bound the degrees and lengths in an acyclic system by consecutive splits. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

variable {V I : Type*} [LinearOrder V] [LinearOrder I]

/-- Enough slots for partitioning a finite ordered set into blocks of width w. -/
def blockCount (S : Finset V) (w : ℕ) : ℕ := S.card / w + 1

/-- One block of consecutive positions in S. -/
def orderBlock (S : Finset V) (w j : ℕ) : Finset V :=
  S.filter fun v => (predecessors S v).card / w = j

theorem orderBlock_card (S : Finset V) {w : ℕ} (hw : 0 < w) (j : ℕ) :
    (orderBlock S w j).card ≤ w := by
  let rank (x : V) := (predecessors S x).card
  calc
    _ ≤ (range w).card := by
      apply card_le_card_of_injOn (fun v => rank v % w)
      · intro v _
        exact mem_range.mpr (Nat.mod_lt _ hw)
      · intro u hu v hv eq
        change rank u % w = rank v % w at eq
        obtain ⟨hu, qu⟩ := mem_filter.mp hu
        obtain ⟨hv, qv⟩ := mem_filter.mp hv
        have eu := Nat.mod_add_div (rank u) w
        have ev := Nat.mod_add_div (rank v) w
        change rank u / w = j at qu
        change rank v / w = j at qv
        rw [qu] at eu
        rw [qv] at ev
        exact predecessor_count_injective S hu hv (show rank u = rank v by omega)
    _ = _ := card_range _

private theorem block_index_lt (S : Finset V) (w : ℕ) (v : V) :
    (predecessors S v).card / w < blockCount S w :=
  Nat.lt_succ_of_le (Nat.div_le_div_right (card_filter_le _ _))

private theorem orderBlock_sum (S : Finset V) (w : ℕ) :
    (∑ j : Fin (blockCount S w), (orderBlock S w j.val).card) = S.card := by
  have h := card_eq_sum_card_fiberwise (s := S) (t := range (blockCount S w))
    (f := fun v => (predecessors S v).card / w) (fun v _ => mem_range.mpr (block_index_lt S w v))
  calc
    _ = ∑ j ∈ range (blockCount S w), (orderBlock S w j).card := Fin.sum_univ_eq_sum_range _ _
    _ = _ := h.symm

/-- The copy indices for splitting each member of an indexed family into ordered blocks. -/
abbrev BlockIndex (sets : I → Finset V) (w : ℕ) := Σₗ i : I, Fin (blockCount (sets i) w)

omit [LinearOrder V] in
/-- Ordering blocks lexicographically retains their parent order. -/
theorem block_parent_mono (sets : I → Finset V) (w : ℕ) :
    Monotone (fun i : BlockIndex sets w => i.fst) := by
  intro i j h
  rcases Sigma.Lex.le_def.mp h with hlt | ⟨eq, _⟩
  · exact hlt.le
  · exact eq.le

/-- Split each path into its consecutive blocks, keeping the parent path order. -/
def splitPaths (paths : I → Finset V) (w : ℕ) (i : BlockIndex paths w) : Finset V :=
  orderBlock (paths i.fst) w i.snd.val

omit [LinearOrder I] in
private theorem splitPaths_subset (paths : I → Finset V) (w : ℕ) (i : BlockIndex paths w) :
    splitPaths paths w i ⊆ paths i.fst :=
  filter_subset _ _

omit [LinearOrder I] in
private theorem splitPaths_disjoint {paths : I → Finset V} {w : ℕ}
    (i j : BlockIndex paths w) (hne : i ≠ j) (parent : i.fst = j.fst) :
    Disjoint (splitPaths paths w i) (splitPaths paths w j) := by
  apply disjoint_left.mpr
  intro v hi hj
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  change i = j at parent
  subst j
  have ha : (predecessors (paths i) v).card / w = a.val := (mem_filter.mp hi).2
  have hb : (predecessors (paths i) v).card / w = b.val := (mem_filter.mp hj).2
  obtain rfl := Fin.ext (ha.symm.trans hb)
  exact hne rfl

omit [LinearOrder I] in
private theorem splitPaths_convex {paths : I → Finset V} {w : ℕ}
    (i : BlockIndex paths w) {x y z : V} (hx : x ∈ splitPaths paths w i) (hz : z ∈ splitPaths paths w i)
    (hy : y ∈ paths i.fst) (hxy : x ≤ y) (hyz : y ≤ z) : y ∈ splitPaths paths w i := by
  apply mem_filter.mpr
  refine ⟨hy, ?_⟩
  have le₁ := Nat.div_le_div_right (predecessor_count_mono (paths i.fst) hxy) (c := w)
  have le₂ := Nat.div_le_div_right (predecessor_count_mono (paths i.fst) hyz) (c := w)
  rw [(mem_filter.mp hx).2] at le₁
  rw [(mem_filter.mp hz).2] at le₂
  exact le_antisymm le₂ le₁

theorem splitPaths_halfFree {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (w : ℕ) : HalfBridgeFree (PathBefore (splitPaths paths w)) 4 :=
  free.split_paths Sigma.fst (block_parent_mono paths w) (splitPaths_subset paths w)
    splitPaths_disjoint splitPaths_convex

theorem splitPaths_free {paths : I → Finset V} (free : BridgeFree (PathBefore paths) 4)
    (w : ℕ) : BridgeFree (PathBefore (splitPaths paths w)) 4 :=
  free.split_paths Sigma.fst (splitPaths_subset paths w) splitPaths_disjoint splitPaths_convex

omit [LinearOrder I] in
theorem splitPaths_length (paths : I → Finset V) {w : ℕ} (hw : 0 < w) (i : BlockIndex paths w) :
    (splitPaths paths w i).card ≤ w :=
  orderBlock_card _ hw _

variable [Fintype I]

omit [LinearOrder I] in
theorem splitPaths_size (paths : I → Finset V) (w : ℕ) :
    (∑ j : BlockIndex paths w, (splitPaths paths w j).card) = ∑ i, (paths i).card := by
  change (∑ j : (Σ i : I, Fin (blockCount (paths i) w)), (orderBlock (paths j.1) w j.2.val).card) = _
  rw [Fintype.sum_sigma]
  exact sum_congr rfl fun i _ => orderBlock_sum (paths i) w

theorem splitPaths_degree (paths : I → Finset V) (w : ℕ) (v : V) :
    (occurrences (splitPaths paths w) v).card ≤ (occurrences paths v).card := by
  apply card_le_card_of_injOn (fun i : BlockIndex paths w => i.fst)
  · intro i hi
    exact mem_occurrences.mpr (splitPaths_subset paths w i (mem_occurrences.mp hi))
  · intro i hi j hj eq
    by_contra hne
    exact disjoint_left.mp (splitPaths_disjoint i j hne eq) (mem_occurrences.mp hi) (mem_occurrences.mp hj)

omit [LinearOrder V] [LinearOrder I] in
theorem blockIndex_card_bound (sets : I → Finset V) {w : ℕ} (hw : 0 < w)
    (mass : (∑ i, (sets i).card) ≤ Fintype.card I*w) :
    Fintype.card (BlockIndex sets w) ≤ 2 * Fintype.card I := by
  rw [Fintype.card_lex, Fintype.card_sigma]
  have count (i : I) : Fintype.card (Fin (blockCount (sets i) w)) = (sets i).card / w + 1 :=
    Fintype.card_fin _
  simp only [count, sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one]
  have eq : (∑ i, (sets i).card / w)*w ≤ Fintype.card I*w := by
    rw [sum_mul]
    exact (sum_le_sum (fun i _ => Nat.div_mul_le_self (sets i).card w)).trans mass
  have le := Nat.le_of_mul_le_mul_right eq hw
  omega

omit [LinearOrder V] [LinearOrder I] in
theorem blockIndex_card_ge (sets : I → Finset V) (w : ℕ) :
    Fintype.card I ≤ Fintype.card (BlockIndex sets w) :=
  Fintype.card_le_of_injective
    (fun i => (⟨i, ⟨0, Nat.succ_pos _⟩⟩ : BlockIndex sets w))
    (fun _ _ eq => congrArg Sigma.fst eq)

/-- The ordered copies of each vertex, indexed by blocks of its incident paths. -/
abbrev VertexBlockIndex (paths : I → Finset V) (w : ℕ) := BlockIndex (occurrences paths) w

/-- The copy of a vertex assigned to its occurrence in a path. -/
def vertexCopy (paths : I → Finset V) (w : ℕ) (i : I) (v : paths i) :
    VertexBlockIndex paths w :=
  ⟨v.val, ⟨(predecessors (occurrences paths v.val) i).card / w,
    block_index_lt (occurrences paths v.val) w i⟩⟩

/-- Replace a vertex on a path by the copy for that block of incident paths. -/
def splitVertices (paths : I → Finset V) (w : ℕ) (i : I) : Finset (VertexBlockIndex paths w) :=
  (paths i).attach.map ⟨vertexCopy paths w i,
    fun _ _ eq => Subtype.ext (congrArg Sigma.fst eq)⟩

private theorem splitVertices_projects (paths : I → Finset V) (w : ℕ) (i : I) :
    Set.MapsTo (fun v : VertexBlockIndex paths w => v.fst) (splitVertices paths w i) (paths i) := by
  intro v hv
  obtain ⟨u, _, rfl⟩ := mem_map.mp hv
  exact u.2

private theorem splitVertices_injective (paths : I → Finset V) (w : ℕ) (i : I) :
    Set.InjOn (fun v : VertexBlockIndex paths w => v.fst) (splitVertices paths w i) := by
  intro u hu v hv eq
  obtain ⟨a, _, rfl⟩ := mem_map.mp hu
  obtain ⟨b, _, rfl⟩ := mem_map.mp hv
  exact congrArg (vertexCopy paths w i) (Subtype.ext eq)

theorem splitVertices_halfFree {paths : I → Finset V} {k : ℕ}
    (free : HalfBridgeFree (PathBefore paths) k) (w : ℕ) :
    HalfBridgeFree (PathBefore (splitVertices paths w)) k :=
  free.split_vertices Sigma.fst (block_parent_mono (occurrences paths) w)
    (splitVertices_projects paths w) (splitVertices_injective paths w)

theorem splitVertices_free {paths : I → Finset V} {k : ℕ}
    (free : BridgeFree (PathBefore paths) k) (w : ℕ) :
    BridgeFree (PathBefore (splitVertices paths w)) k :=
  free.split_vertices Sigma.fst (block_parent_mono (occurrences paths) w)
    (splitVertices_projects paths w) (splitVertices_injective paths w)

theorem splitVertices_length (paths : I → Finset V) (w : ℕ) (i : I) :
    (splitVertices paths w i).card = (paths i).card := by
  simp [splitVertices]

theorem splitVertices_degree (paths : I → Finset V) {w : ℕ} (hw : 0 < w) (v : VertexBlockIndex paths w) :
    (occurrences (splitVertices paths w) v).card ≤ w := by
  refine (card_le_card (t := orderBlock (occurrences paths v.fst) w v.snd.val) ?_).trans
    (orderBlock_card _ hw _)
  intro i hi
  have hv := mem_occurrences.mp hi
  unfold splitVertices at hv
  obtain ⟨u, _, rfl⟩ := mem_map.mp hv
  exact mem_filter.mpr ⟨mem_occurrences.mpr u.2, rfl⟩

variable [Fintype V]

omit [LinearOrder I] in
theorem splitVertices_card (paths : I → Finset V) {w : ℕ} (hw : 0 < w)
    (mass : (∑ i, (paths i).card) ≤ Fintype.card V*w) :
    Fintype.card (VertexBlockIndex paths w) ≤ 2*Fintype.card V := by
  apply blockIndex_card_bound (occurrences paths) hw
  rw [sum_occurrences]
  exact mass

omit [Fintype V] in
theorem regularization_halfFree {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (D L : ℕ) : HalfBridgeFree (PathBefore (splitPaths (splitVertices paths D) L)) 4 :=
  splitPaths_halfFree (splitVertices_halfFree free D) L

omit [Fintype V] in
theorem regularization_free {paths : I → Finset V} (free : BridgeFree (PathBefore paths) 4)
    (D L : ℕ) : BridgeFree (PathBefore (splitPaths (splitVertices paths D) L)) 4 :=
  splitPaths_free (splitVertices_free free D) L

/-- Splitting first by degree and then by length keeps every incidence, with
at most twice as many vertices and paths. -/
theorem regularization_size (paths : I → Finset V) (D L : ℕ) (hD : 0 < D) (hL : 0 < L)
    (degree_mass : (∑ i, (paths i).card) ≤ Fintype.card V*D)
    (length_mass : (∑ i, (paths i).card) ≤ Fintype.card I*L) :
    let afterVertices := splitVertices paths D
    let after := splitPaths afterVertices L
    Fintype.card (VertexBlockIndex paths D) ≤ 2*Fintype.card V ∧
      Fintype.card (BlockIndex afterVertices L) ≤ 2*Fintype.card I ∧
      (∑ i, (after i).card) = ∑ i, (paths i).card ∧
      (∀ i, (after i).card ≤ L) ∧
      ∀ v, (occurrences after v).card ≤ D := by
  have same : (∑ i, (splitVertices paths D i).card) = ∑ i, (paths i).card := by
    simp only [splitVertices_length]
  exact ⟨splitVertices_card paths hD degree_mass,
    blockIndex_card_bound _ hL (same.le.trans length_mass),
    (splitPaths_size _ _).trans same, fun i => splitPaths_length _ hL i,
    fun v => (splitPaths_degree _ _ v).trans (splitVertices_degree paths hD v)⟩

/-- One plus the integer part of an average remains within four times
that average when its count grows by at most a factor of two. -/
theorem averageWidth_times_card_le {M count expanded : ℕ} (enough : count ≤ M)
    (size : expanded ≤ 2 * count) : (M / count + 1) * expanded ≤ 4 * M := by
  have width : (M / count + 1) * count ≤ 2 * M := by
    rw [Nat.add_mul, one_mul]
    have h := Nat.div_mul_le_self M count
    omega
  calc
    _ ≤ (M / count + 1) * (2 * count) := Nat.mul_le_mul_left _ size
    _ = 2 * ((M / count + 1) * count) := by ring
    _ ≤ _ := by omega

/-- The degree and length caps from one plus the original average integer part
are within four times the new averages after splitting. -/
theorem regularization_average_caps (paths : I → Finset V)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (dense : Fintype.card V ≤ ∑ i, (paths i).card)
    (long : Fintype.card I ≤ ∑ i, (paths i).card) :
    let M := ∑ i, (paths i).card
    let D := M / Fintype.card V + 1
    let L := M / Fintype.card I + 1
    let afterVertices := splitVertices paths D
    let after := splitPaths afterVertices L
    Fintype.card (VertexBlockIndex paths D) ≤ 2*Fintype.card V ∧
      Fintype.card (BlockIndex afterVertices L) ≤ 2*Fintype.card I ∧
      (∑ i, (after i).card) = M ∧
      (∀ i, (after i).card ≤ L) ∧
      (∀ v, (occurrences after v).card ≤ D) ∧
      D*Fintype.card (VertexBlockIndex paths D) ≤ 4*M ∧
      L*Fintype.card (BlockIndex afterVertices L) ≤ 4*M := by
  let M := ∑ i, (paths i).card
  let n := Fintype.card V
  let p := Fintype.card I
  let D := M/n + 1
  let L := M/p + 1
  have mD : M ≤ n*D := (Nat.lt_mul_div_succ M hn).le
  have mL : M ≤ p*L := (Nat.lt_mul_div_succ M hp).le
  obtain ⟨hn', hp', hs, hl, hd⟩ := regularization_size paths D L
    (Nat.succ_pos (M/n)) (Nat.succ_pos (M/p)) mD mL
  exact ⟨hn', hp', hs, hl, hd, averageWidth_times_card_le dense hn', averageWidth_times_card_le long hp'⟩

end OnlineReachabilityPreservers
