import DirectedFlowCutGap.UnitCostReduction

/-!
# A finite reduction to uniform vertex weights

This repairs the chain construction in Theorem 28 of arXiv:2604.03412v3.
Every fiber has `max 1 ceil(weight/average)` vertices, including zero-weight
vertices. Edges traverse fibers in order and original arcs join the last
copy to the first copy. Projection uses actual walks and loop erasure;
full-fiber traversal is proved from the adjacency relation.

Permanent terminal ports make the integral-cut bridge uniform, including
length-zero paths. The resulting concrete instance has at most `6n`
vertices and total uniform weight at most `2W`. No running-time or
exact-parameter monotonicity claim is made.
-/

namespace DirectedFlowCutGap
noncomputable section
open scoped BigOperators NNReal ENNReal
namespace UniformWeightReduction

universe u
variable {V : Type u}

abbrev Vertex (k : V → ℕ) := Σ v : V, Fin (k v)

def first (k : V → ℕ) (hk : ∀ v, 1 ≤ k v) (v : V) : Vertex k :=
  ⟨v, ⟨0, hk v⟩⟩

def last (k : V → ℕ) (hk : ∀ v, 1 ≤ k v) (v : V) : Vertex k :=
  ⟨v, ⟨k v - 1, by have := hk v; omega⟩⟩

/-- Consecutive chain edges and the original arcs between fiber ends. -/
def graph (G : Digraph V) (k : V → ℕ) : Digraph (Vertex k) where
  Adj a b := (a.1 = b.1 ∧ b.2.val = a.2.val + 1) ∨
    (a.2.val + 1 = k a.1 ∧ b.2.val = 0 ∧ G.Adj a.1 b.1)

/-- Equality of clones is equality of their originals and their indices. -/
theorem vertex_ext {k : V → ℕ} {a b : Vertex k}
    (hf : a.1 = b.1) (hi : a.2.val = b.2.val) : a = b := by
  rcases a with ⟨v, i⟩
  rcases b with ⟨u, j⟩
  dsimp at hf hi
  subst u
  exact congrArg (fun i : Fin (k v) => (⟨v, i⟩ : Vertex k)) (Fin.ext hi)

@[simp] theorem first_fst (k : V → ℕ) (hk : ∀ v, 1 ≤ k v) (v : V) :
    (first k hk v).1 = v := rfl
@[simp] theorem last_fst (k : V → ℕ) (hk : ∀ v, 1 ≤ k v) (v : V) :
    (last k hk v).1 = v := rfl

theorem arc {G : Digraph V} {k : V → ℕ} (hk : ∀ v, 1 ≤ k v)
    {s t : V} (h : G.Adj s t) : (graph G k).Adj (last k hk s) (first k hk t) := by
  right
  exact ⟨by dsimp [last]; have := hk s; omega, rfl, h⟩

variable [DecidableEq V]

/-- All copies of the given finite collection of originals. -/
def fibers (k : V → ℕ) (X : Finset V) : Finset (Vertex k) :=
  X.sigma fun v => Finset.univ

@[simp] theorem mem_fibers (k : V → ℕ) (X : Finset V) (a : Vertex k) :
    a ∈ fibers k X ↔ a.1 ∈ X := by simp [fibers]

/-- A genuine directed simple path traversing a whole fiber. -/
def chainPath (G : Digraph V) (k : V → ℕ) (hk : ∀ v, 1 ≤ k v) (v : V) :
    SimplePath (graph G k) (first k hk v) (last k hk v) where
  edgeLength := k v - 1
  vertex i := ⟨v, ⟨i.val, by have := hk v; have := i.isLt; omega⟩⟩
  source_eq := rfl
  target_eq := rfl
  injective := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun a : Vertex k => a.2.val) h
  adjacent := by
    intro i
    exact Or.inl ⟨rfl, rfl⟩

theorem chainPath_vertices (G : Digraph V) (k : V → ℕ)
    (hk : ∀ v, 1 ≤ k v) (v : V) :
    (chainPath G k hk v).vertices ⊆ fibers k {v} := by
  intro a ha
  obtain ⟨i, rfl⟩ := (SimplePath.mem_vertices _ _).mp ha
  simp [chainPath]

/-- Expand an actual walk, inserting each whole chain between original arcs. -/
theorem exists_expandedWalk {G : Digraph V} {k : V → ℕ}
    (hk : ∀ v, 1 ≤ k v) {s t : V} (p : DirectedWalk G s t) :
    ∃ q : DirectedWalk (graph G k) (first k hk s) (last k hk t),
      q.vertices ⊆ fibers k p.vertices := by
  induction p with
  | refl s =>
    obtain ⟨q, hq⟩ := (chainPath G k hk s).exists_directedWalk
    exact ⟨q, hq.trans (chainPath_vertices G k hk s)⟩
  | @cons s v t h p ih =>
    obtain ⟨q, hq⟩ := ih
    obtain ⟨c, hc⟩ := (chainPath G k hk s).exists_directedWalk
    refine ⟨c.append (.cons (arc hk h) q), ?_⟩
    rw [DirectedWalk.append_vertices]
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have hs := (mem_fibers k {s} a).mp ((hc.trans (chainPath_vertices G k hk s)) ha)
      apply (mem_fibers _ _ _).mpr
      exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hs))
    · simp only [DirectedWalk.vertices, Finset.mem_insert] at ha
      rcases ha with rfl | ha
      · simp [DirectedWalk.vertices]
      · exact (mem_fibers _ _ _).mpr (Finset.mem_insert_of_mem ((mem_fibers _ _ _).mp (hq ha)))

/-- With singleton endpoint fibers, the expanded lift has no extra internal
copies of either endpoint. Permanent ports satisfy these hypotheses. -/
theorem exists_lift {G : Digraph V} {k : V → ℕ} (hk : ∀ v, 1 ≤ k v)
    {s t : V} (hs : k s = 1) (ht : k t = 1) (p : SimplePath G s t) :
    ∃ q : SimplePath (graph G k) (last k hk s) (first k hk t),
      q.internalVertices ⊆ fibers k p.internalVertices := by
  have hes : first k hk s = last k hk s := by
    apply congrArg (fun i : Fin (k s) => (⟨s, i⟩ : Vertex k))
    apply Fin.ext
    simp [first, last, hs]
  have het : last k hk t = first k hk t := by
    apply congrArg (fun i : Fin (k t) => (⟨t, i⟩ : Vertex k))
    apply Fin.ext
    simp [first, last, ht]
  obtain ⟨a, ha⟩ := p.exists_directedWalk
  have hwalk : ∃ b : DirectedWalk (graph G k) (last k hk s) (first k hk t),
      b.vertices ⊆ fibers k a.vertices := by
    exact (congrArg₂ (fun x y : Vertex k =>
      ∃ b : DirectedWalk (graph G k) x y, b.vertices ⊆ fibers k a.vertices) hes het).mp
        (exists_expandedWalk hk a)
  obtain ⟨b, hb⟩ := hwalk
  obtain ⟨q, hq⟩ := b.exists_simplePath
  refine ⟨q, ?_⟩
  intro x hx
  obtain ⟨hxm, hxs, hxt⟩ := (q.mem_internalVertices x).mp hx
  have hxp := ha ((mem_fibers _ _ _).mp (hb (hq ((q.mem_vertices x).mpr hxm))))
  apply (mem_fibers _ _ _).mpr
  apply (p.mem_internalVertices _).mpr
  refine ⟨(p.mem_vertices _).mp hxp, ?_, ?_⟩
  · intro he
    apply hxs
    rcases x with ⟨v, i⟩
    dsimp at he
    subst v
    apply congrArg (fun i : Fin (k s) => (⟨s, i⟩ : Vertex k))
    apply Fin.ext
    have := i.isLt
    simp only [hs] at this
    dsimp [last]
    omega
  · intro he
    apply hxt
    rcases x with ⟨v, i⟩
    dsimp at he
    subst v
    apply congrArg (fun i : Fin (k t) => (⟨t, i⟩ : Vertex k))
    apply Fin.ext
    have := i.isLt
    simp only [ht] at this
    dsimp [first]
    omega

/-- Every nonfirst clone on a path has its immediate predecessor on that path
unless its original is the source's original. -/
theorem predecessor_mem {G : Digraph V} {k : V → ℕ} {a b : Vertex k}
    (q : SimplePath (graph G k) a b) (v : V) (hv : v ≠ a.1)
    (i : Fin (k v)) (hi : 0 < i.val) (hm : (⟨v, i⟩ : Vertex k) ∈ q.vertices) :
    (⟨v, ⟨i.val - 1, by omega⟩⟩ : Vertex k) ∈ q.vertices := by
  obtain ⟨j, hj⟩ := (q.mem_vertices _).mp hm
  have hjpos : 0 < j.val := by
    by_contra hn
    have he : j = 0 := by
      apply Fin.ext
      change j.val = 0
      omega
    have hh := congrArg Sigma.fst (hj.symm.trans ((congrArg q.vertex he).trans q.source_eq))
    exact hv hh
  let r : Fin q.edgeLength := ⟨j.val - 1, by omega⟩
  have hr : r.succ = j := Fin.ext (by dsimp [r]; omega)
  have he := q.adjacent r
  rw [hr, hj] at he
  rcases he with ⟨hf, hi'⟩ | ⟨_, hz, _⟩
  · apply (q.mem_vertices _).mpr
    refine ⟨r.castSucc, ?_⟩
    apply vertex_ext
    · exact hf
    · dsimp at hi' ⊢
      omega
  · dsimp at hz
    omega

/-- Similarly every nonlast clone has its immediate successor on the path. -/
theorem successor_mem {G : Digraph V} {k : V → ℕ} {a b : Vertex k}
    (q : SimplePath (graph G k) a b) (v : V) (hv : v ≠ b.1)
    (i : Fin (k v)) (hi : i.val + 1 < k v)
    (hm : (⟨v, i⟩ : Vertex k) ∈ q.vertices) :
    (⟨v, ⟨i.val + 1, hi⟩⟩ : Vertex k) ∈ q.vertices := by
  obtain ⟨j, hj⟩ := (q.mem_vertices _).mp hm
  have hjlt : j.val < q.edgeLength := by
    by_contra hn
    have he : j = Fin.last q.edgeLength := Fin.ext (by simp; omega)
    have hh := congrArg Sigma.fst (hj.symm.trans ((congrArg q.vertex he).trans q.target_eq))
    exact hv hh
  let r : Fin q.edgeLength := ⟨j.val, hjlt⟩
  have hr : r.castSucc = j := Fin.ext rfl
  have he := q.adjacent r
  rw [hr, hj] at he
  rcases he with ⟨hf, hi'⟩ | ⟨hz, _, _⟩
  · apply (q.mem_vertices _).mpr
    refine ⟨r.succ, ?_⟩
    exact vertex_ext hf.symm hi' 
  · dsimp at hz
    omega

/-- Visiting any clone of a nonendpoint original forces visiting its whole
chain. This is derived from actual consecutive edges, not a correspondence axiom. -/
theorem full_fiber_mem {G : Digraph V} {k : V → ℕ} {a b : Vertex k}
    (q : SimplePath (graph G k) a b) (v : V) (hs : v ≠ a.1) (ht : v ≠ b.1)
    (i : Fin (k v)) (hm : (⟨v, i⟩ : Vertex k) ∈ q.vertices) :
    ∀ j : Fin (k v), (⟨v, j⟩ : Vertex k) ∈ q.internalVertices := by
  have hzero : (⟨v, ⟨0, (by have := i.isLt; omega)⟩⟩ : Vertex k) ∈ q.vertices := by
    have aux : ∀ n, ∀ z : Fin (k v), z.val = n →
        (⟨v, z⟩ : Vertex k) ∈ q.vertices →
        (⟨v, ⟨0, (by have := i.isLt; omega)⟩⟩ : Vertex k) ∈ q.vertices := by
      intro n
      induction n with
      | zero =>
        intro z hz hzm
        have he : z = ⟨0, (by have := i.isLt; omega)⟩ := Fin.ext hz
        simpa only [he] using hzm
      | succ n ih =>
        intro z hz hzm
        exact ih ⟨z.val - 1, by omega⟩ (by simp [hz])
          (predecessor_mem q v hs z (by omega) hzm)
    exact aux i.val i rfl hm
  have hall : ∀ j : Fin (k v), (⟨v, j⟩ : Vertex k) ∈ q.vertices := by
    intro j
    have aux : ∀ n, ∀ hn : n < k v, (⟨v, ⟨n, hn⟩⟩ : Vertex k) ∈ q.vertices := by
      intro n
      induction n with
      | zero => intro hn; exact hzero
      | succ n ih =>
        intro hn
        exact successor_mem q v ht ⟨n, by omega⟩ hn (ih (by omega))
    exact aux j.val j.isLt
  intro j
  apply (q.mem_internalVertices _).mpr
  exact ⟨(q.mem_vertices _).mp (hall j),
    fun he => hs (congrArg Sigma.fst he), fun he => ht (congrArg Sigma.fst he)⟩

private def reflexiveGraph (G : Digraph V) : Digraph V where
  Adj a b := a = b ∨ G.Adj a b

private def projectWalk {G : Digraph V} {k : V → ℕ} {a b : Vertex k}
    (q : DirectedWalk (graph G k) a b) : DirectedWalk (reflexiveGraph G) a.1 b.1 :=
  match q with
  | .refl a => .refl a.1
  | .cons h q => .cons (h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2.2)) (projectWalk q)

private theorem projectWalk_vertices {G : Digraph V} {k : V → ℕ} {a b : Vertex k}
    (q : DirectedWalk (graph G k) a b) :
    (projectWalk q).vertices = q.vertices.image Sigma.fst := by
  induction q with
  | refl => simp [projectWalk, DirectedWalk.vertices]
  | cons h q ih => simp [projectWalk, DirectedWalk.vertices, ih]

private theorem erase_reflexive_steps {G : Digraph V} {s t : V}
    (q : DirectedWalk (reflexiveGraph G) s t) :
    ∃ p : DirectedWalk G s t, p.vertices ⊆ q.vertices := by
  induction q with
  | refl s => exact ⟨.refl s, Finset.Subset.refl _⟩
  | @cons s v t h q ih =>
    obtain ⟨p, hp⟩ := ih
    rcases h with he | he
    · subst v
      exact ⟨p, hp.trans (Finset.subset_insert _ _)⟩
    · exact ⟨.cons he p, Finset.insert_subset_insert _ hp⟩

/-- Every expanded path projects to a real original simple path, and all
copies of its internal originals occur internally on the expanded path. -/
theorem exists_projection {G : Digraph V} {k : V → ℕ} {a b : Vertex k}
    (q : SimplePath (graph G k) a b) :
    ∃ p : SimplePath G a.1 b.1, fibers k p.internalVertices ⊆ q.internalVertices := by
  obtain ⟨c, hc⟩ := q.exists_directedWalk
  obtain ⟨d, hd⟩ := erase_reflexive_steps (projectWalk c)
  obtain ⟨p, hp⟩ := d.exists_simplePath
  refine ⟨p, ?_⟩
  intro x hx
  have hx' := (mem_fibers _ _ _).mp hx
  obtain ⟨hxp, hxs, hxt⟩ := (p.mem_internalVertices x.1).mp hx'
  have hm := hd (hp ((p.mem_vertices _).mpr hxp))
  rw [projectWalk_vertices] at hm
  obtain ⟨⟨v, i⟩, hi, he⟩ := Finset.mem_image.mp hm
  dsimp at he
  rcases x with ⟨x, j⟩
  dsimp at he hxs hxt
  subst v
  exact full_fiber_mem q x hxs hxt i (hc hi) j

/-- Exact weight of a union of complete fibers. -/
theorem sum_fibers (k : V → ℕ) (X : Finset V) (δ : ℝ≥0) :
    (∑ _a ∈ fibers k X, δ) = ∑ v ∈ X, (k v : ℝ≥0) * δ := by
  simp [fibers, nsmul_eq_mul, Finset.sum_mul]

/-- Uniform chain mass dominates every original internal vertex's weight. -/
theorem exists_projection_weight_le {G : Digraph V} {k : V → ℕ}
    {a b : Vertex k} (q : SimplePath (graph G k) a b)
    (w : V → ℝ≥0) (δ : ℝ≥0) (hw : ∀ v, w v ≤ (k v : ℝ≥0) * δ) :
    ∃ p : SimplePath G a.1 b.1, fibers k p.internalVertices ⊆ q.internalVertices ∧
      p.weight w ≤ q.weight (fun _ => δ) := by
  obtain ⟨p, hp⟩ := exists_projection q
  refine ⟨p, hp, ?_⟩
  calc
    p.weight w ≤ ∑ v ∈ p.internalVertices, (k v : ℝ≥0) * δ :=
      Finset.sum_le_sum (fun v _ => hw v)
    _ = ∑ _a ∈ fibers k p.internalVertices, δ := (sum_fibers _ _ _).symm
    _ ≤ q.weight (fun _ => δ) := Finset.sum_le_sum_of_subset hp

/-- Pull back any selected clone, rather than requiring a fully deleted fiber. -/
def pullback {k : V → ℕ} (Y : Finset (Vertex k)) : Finset V := Y.image Sigma.fst

@[simp] theorem mem_pullback {k : V → ℕ} (Y : Finset (Vertex k)) (v : V) :
    v ∈ pullback Y ↔ ∃ i : Fin (k v), (⟨v, i⟩ : Vertex k) ∈ Y := by
  simp only [pullback, Finset.mem_image]
  constructor
  · rintro ⟨⟨u, i⟩, hi, he⟩
    dsimp at he
    subst u
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨⟨v, i⟩, hi, rfl⟩

theorem card_pullback_le {k : V → ℕ} (Y : Finset (Vertex k)) :
    (pullback Y).card ≤ Y.card := Finset.card_image_le

/-- An actual avoiding lift proves integral pullback for singleton endpoints. -/
theorem cutsPair_pullback {G : Digraph V} {k : V → ℕ} (hk : ∀ v, 1 ≤ k v)
    {s t : V} (hs : k s = 1) (ht : k t = 1) (Y : Finset (Vertex k))
    (hY : CutsPair (graph G k) Y (last k hk s) (first k hk t)) :
    CutsPair G (pullback Y) s t := by
  intro p
  obtain ⟨q, hq⟩ := exists_lift hk hs ht p
  obtain ⟨x, hx, hxy⟩ := hY q
  exact ⟨x.1, (mem_fibers _ _ _).mp (hq hx), Finset.mem_image.mpr ⟨x, hxy, rfl⟩⟩

/-- Demand endpoints use the last source clone and first target clone. -/
def chainDemands (k : V → ℕ) (hk : ∀ v, 1 ≤ k v) (D : Set (V × V)) :
    Set (Vertex k × Vertex k) :=
  (fun st => (last k hk st.1, first k hk st.2)) '' D

/-- The direct chain gadget preserves fractional feasibility even before
permanent ports are introduced. -/
theorem isFractionalCut_chain {G : Digraph V} {k : V → ℕ}
    (hk : ∀ v, 1 ≤ k v) (w : V → ℝ≥0) (δ : ℝ≥0)
    (hw : ∀ v, w v ≤ (k v : ℝ≥0) * δ) {D : Set (V × V)}
    (hf : IsFractionalCut G w D) :
    IsFractionalCut (graph G k) (fun _ => δ) (chainDemands k hk D) := by
  rw [isFractionalCut_iff] at hf ⊢
  intro a b hab q
  obtain ⟨⟨s, t⟩, hst, he⟩ := hab
  have ha : last k hk s = a := congrArg Prod.fst he
  have hb : first k hk t = b := congrArg Prod.snd he
  subst a
  subst b
  obtain ⟨p, _, hp⟩ := exists_projection_weight_le q w δ hw
  exact (hf s t hst p).trans hp

variable [Fintype V]

/-- The finite average, defined even in the empty or zero-total case. -/
def average (w : V → ℝ≥0) : ℝ≥0 := totalWeight w / (Fintype.card V : ℝ≥0)

def copies (w : V → ℝ≥0) (v : V) : ℕ := max 1 ⌈w v / average w⌉₊

theorem copies_pos (w : V → ℝ≥0) (v : V) : 1 ≤ copies w v := le_max_left _ _

@[simp] theorem copies_zero {w : V → ℝ≥0} {v : V} (h : w v = 0) : copies w v = 1 := by
  simp [copies, h]

theorem average_pos (w : V → ℝ≥0) (hW : 0 < totalWeight w) : 0 < average w := by
  have hn : 0 < Fintype.card V := by
    by_contra h
    haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h)
    simp [totalWeight] at hW
  exact div_pos hW (by exact_mod_cast hn)

theorem weight_le_copies (w : V → ℝ≥0) (hW : 0 < totalWeight w) (v : V) :
    w v ≤ (copies w v : ℝ≥0) * average w := by
  apply (div_le_iff₀ (average_pos w hW)).mp
  exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈w v / average w⌉₊))

theorem copies_le_ratio_add_one (w : V → ℝ≥0) (v : V) :
    (copies w v : ℝ≥0) ≤ w v / average w + 1 := by
  rw [copies, Nat.cast_max, Nat.cast_one]
  exact max_le (by simp) (Nat.ceil_lt_add_one (show 0 ≤ w v / average w from zero_le)).le

@[simp] theorem card_vertex (k : V → ℕ) : Fintype.card (Vertex k) = ∑ v, k v := by
  simp [Vertex, Fintype.card_sigma]

@[simp] theorem totalWeight_uniform (k : V → ℕ) (δ : ℝ≥0) :
    totalWeight (fun _ : Vertex k => δ) = (Fintype.card (Vertex k) : ℝ≥0) * δ := by
  simp [totalWeight, nsmul_eq_mul]

/-- The actual number of copies is at most twice the original cardinality. -/
theorem copied_card_le (w : V → ℝ≥0) (hW : 0 < totalWeight w) :
    Fintype.card (Vertex (copies w)) ≤ 2 * Fintype.card V := by
  have ha := average_pos w hW
  have hn : (Fintype.card V : ℝ≥0) ≠ 0 := by
    intro h
    simp [average, h] at ha
  have he : totalWeight w / average w = (Fintype.card V : ℝ≥0) := by
    dsimp [average]
    field_simp [ne_of_gt hW]
  have hb : (Fintype.card (Vertex (copies w)) : ℝ≥0) ≤ 2 * (Fintype.card V : ℝ≥0) := by
    rw [card_vertex, Nat.cast_sum]
    calc
      _ ≤ ∑ v, (w v / average w + 1) := Finset.sum_le_sum (fun v _ => copies_le_ratio_add_one w v)
      _ = 2 * (Fintype.card V : ℝ≥0) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div]
        change totalWeight w / average w + _ = _
        rw [he]
        simp [two_mul]
  exact_mod_cast hb

/-- Uniform mass increases by at most a factor of two. -/
theorem copied_totalWeight_le (w : V → ℝ≥0) (hW : 0 < totalWeight w) :
    totalWeight (fun _ : Vertex (copies w) => average w) ≤ 2 * totalWeight w := by
  rw [totalWeight_uniform]
  have hc : (Fintype.card (Vertex (copies w)) : ℝ≥0) ≤ 2 * (Fintype.card V : ℝ≥0) := by
    exact_mod_cast copied_card_le w hW
  calc
    _ ≤ (2 * (Fintype.card V : ℝ≥0)) * average w := mul_le_mul_of_nonneg_right hc zero_le
    _ = 2 * totalWeight w := by
      dsimp [average]
      have hn : (Fintype.card V : ℝ≥0) ≠ 0 := by
        intro he
        have ha := average_pos w hW
        simp [average, he] at ha
      field_simp

/-- Clipping preserves every threshold demand of the input graph. -/
theorem threshold_fractional_clip (G : Digraph V) (w : V → ℝ≥0) :
    IsFractionalCut G (UnitCostReduction.clip w) (thresholdDemands G w) :=
  UnitCostReduction.isFractionalCut_clip (isFractionalCut_thresholdDemands G w)

/-- Prepared cores carry clipped weights and both permanent ports have zero. -/
def preparedWeight (w : V → ℝ≥0) : TerminalPorts.Vertex V → ℝ≥0 :=
  TerminalPorts.extend (UnitCostReduction.clip w)

abbrev ExpandedVertex (w : V → ℝ≥0) := Vertex (copies (preparedWeight w))

def expandedGraph (G : Digraph V) (w : V → ℝ≥0) : Digraph (ExpandedVertex w) :=
  graph (TerminalPorts.graph G) (copies (preparedWeight w))

def uniformWeight (w : V → ℝ≥0) : ExpandedVertex w → ℝ≥0 :=
  fun _ => average (preparedWeight w)

def source (w : V → ℝ≥0) (v : V) : ExpandedVertex w :=
  last _ (copies_pos (preparedWeight w)) (TerminalPorts.source v)

def sink (w : V → ℝ≥0) (v : V) : ExpandedVertex w :=
  first _ (copies_pos (preparedWeight w)) (TerminalPorts.sink v)

def demands (w : V → ℝ≥0) (D : Set (V × V)) :
    Set (ExpandedVertex w × ExpandedVertex w) :=
  (fun st => (source w st.1, sink w st.2)) '' D

def originalCut (w : V → ℝ≥0) (Y : Finset (ExpandedVertex w)) : Finset V :=
  TerminalPorts.corePreimage (pullback Y)

@[simp] theorem source_copies (w : V → ℝ≥0) (v : V) :
    copies (preparedWeight w) (TerminalPorts.source v) = 1 := copies_zero rfl

@[simp] theorem sink_copies (w : V → ℝ≥0) (v : V) :
    copies (preparedWeight w) (TerminalPorts.sink v) = 1 := copies_zero rfl

theorem prepared_fractional {G : Digraph V} {w : V → ℝ≥0}
    {D : Set (V × V)} (hf : IsFractionalCut G w D) :
    IsFractionalCut (TerminalPorts.graph G) (preparedWeight w) (TerminalPorts.demands D) :=
  (TerminalPorts.isFractionalCut_iff G (UnitCostReduction.clip w) D).mpr
    (UnitCostReduction.isFractionalCut_clip hf)

theorem prepared_totalWeight_le (w : V → ℝ≥0) :
    totalWeight (preparedWeight w) ≤ totalWeight w := by
  rw [preparedWeight, TerminalPorts.totalWeight_extend]
  exact Finset.sum_le_sum (fun v _ => min_le_right _ _)

theorem prepared_weight_le_one (w : V → ℝ≥0) (v : TerminalPorts.Vertex V) :
    preparedWeight w v ≤ 1 := by
  cases v with
  | inl v => exact min_le_left _ _
  | inr v => exact zero_le

/-- Clipping also makes the actual uniform weight at most one. -/
theorem uniform_weight_le_one (w : V → ℝ≥0) : average (preparedWeight w) ≤ 1 := by
  by_cases hn : (Fintype.card (TerminalPorts.Vertex V) : ℝ≥0) = 0
  · change totalWeight (preparedWeight w) / (Fintype.card (TerminalPorts.Vertex V) : ℝ≥0) ≤ 1
    rw [hn, div_zero]
    exact zero_le
  · apply (div_le_iff₀ (pos_iff_ne_zero.mpr hn)).mpr
    simp only [one_mul]
    calc
      _ ≤ ∑ _v : TerminalPorts.Vertex V, (1 : ℝ≥0) :=
        Finset.sum_le_sum (fun v _ => prepared_weight_le_one w v)
      _ = _ := by simp

/-- The actual transformed graph has at most six vertices per input vertex. -/
theorem expanded_card_le (w : V → ℝ≥0) (hW : 0 < totalWeight (preparedWeight w)) :
    Fintype.card (ExpandedVertex w) ≤ 6 * Fintype.card V := by
  have h := copied_card_le (preparedWeight w) hW
  rw [TerminalPorts.card_vertex] at h
  exact h.trans_eq (by ring)

/-- The actual transformed graph carries at most twice the original mass. -/
theorem expanded_totalWeight_le (w : V → ℝ≥0) (hW : 0 < totalWeight (preparedWeight w)) :
    totalWeight (uniformWeight w) ≤ 2 * totalWeight w :=
  (copied_totalWeight_le (preparedWeight w) hW).trans
    (mul_le_mul_of_nonneg_left (prepared_totalWeight_le w) zero_le)

/-- Fractionally feasible original demands remain feasible between the
explicit terminal clones in the actual uniform graph. -/
theorem expanded_fractional {G : Digraph V} {w : V → ℝ≥0}
    {D : Set (V × V)} (hf : IsFractionalCut G w D)
    (hW : 0 < totalWeight (preparedWeight w)) :
    IsFractionalCut (expandedGraph G w) (uniformWeight w) (demands w D) := by
  rw [isFractionalCut_iff]
  intro a b hab q
  obtain ⟨⟨s, t⟩, hst, he⟩ := hab
  have ha : source w s = a := congrArg Prod.fst he
  have hb : sink w t = b := congrArg Prod.snd he
  subst a
  subst b
  obtain ⟨p, _, hp⟩ := exists_projection_weight_le q (preparedWeight w)
    (average (preparedWeight w)) (weight_le_copies (preparedWeight w) hW)
  have hfrac := (isFractionalCut_iff _ _ _).mp (prepared_fractional hf)
    (TerminalPorts.source s) (TerminalPorts.sink t) ⟨(s, t), hst, rfl⟩ p
  exact hfrac.trans hp

/-- Pulling selected clones back to cores meets every original demand path. -/
theorem expanded_integral_pullback {G : Digraph V} {w : V → ℝ≥0}
    {D : Set (V × V)} (Y : Finset (ExpandedVertex w))
    (hY : IsIntegralCut (expandedGraph G w) Y (demands w D)) :
    IsIntegralCut G (originalCut w Y) D := by
  intro s t hst
  apply (TerminalPorts.cutsPair_iff G (pullback Y) s t).mp
  exact cutsPair_pullback (copies_pos (preparedWeight w)) (source_copies w s) (sink_copies w t) Y
    (hY (source w s) (sink w t) ⟨(s, t), hst, rfl⟩)

/-- Some-clone pullback and discarding ports both weakly decrease cut size. -/
theorem originalCut_card_le (w : V → ℝ≥0) (Y : Finset (ExpandedVertex w)) :
    (originalCut w Y).card ≤ Y.card := by
  classical
  calc
    _ ≤ (pullback Y).card := by
      have hsub : (originalCut w Y).image TerminalPorts.core ⊆ pullback Y := by
        intro x hx
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
        exact (TerminalPorts.mem_corePreimage _ _).mp hv
      have hinj : Function.Injective (TerminalPorts.core : V → TerminalPorts.Vertex V) :=
        fun _ _ h => Sum.inl.inj h
      calc
        _ = ((originalCut w Y).image TerminalPorts.core).card :=
          (Finset.card_image_of_injective _ hinj).symm
        _ ≤ (pullback Y).card := Finset.card_le_card hsub
    _ ≤ Y.card := card_pullback_le Y

/-- A bounded oracle is asked about actual finite uniform instances, with no
assumption that gaps are monotone in exact parameter values. -/
def BoundedUniformRoundingOracle (N : ℕ) (B α : ℝ≥0) : Prop :=
  ∀ (U : Type u) [Fintype U] [DecidableEq U] (H : Digraph U) (δ : ℝ≥0),
    δ ≤ 1 → Fintype.card U ≤ N → totalWeight (fun _ : U => δ) ≤ B →
    ∃ Y : Finset U, IsIntegralCut H Y (thresholdDemands H (fun _ => δ)) ∧
      (Y.card : ℝ≥0) ≤ α * totalWeight (fun _ : U => δ)

/-- Repaired finite Theorem 28. A uniform-weight rounding oracle for at most
`6n` vertices and mass at most `2W` gives a unit-cost cut of size at most
`2αW`. Clipping preserves demands; zero total weight (including the empty
vertex type) is handled directly without dividing by it. -/
theorem round_of_bounded_uniform_oracle (G : Digraph V) (w : V → ℝ≥0)
    (D : Set (V × V)) (hf : IsFractionalCut G w D) (α : ℝ≥0)
    (oracle : BoundedUniformRoundingOracle.{u} (6 * Fintype.card V) (2 * totalWeight w) α) :
    ∃ X : Finset V, IsIntegralCut G X D ∧ (X.card : ℝ≥0) ≤ 2 * α * totalWeight w := by
  by_cases hW : 0 < totalWeight (preparedWeight w)
  · obtain ⟨Y, hY, hsize⟩ := oracle (ExpandedVertex w) (expandedGraph G w)
      (average (preparedWeight w)) (uniform_weight_le_one w)
      (expanded_card_le w hW) (expanded_totalWeight_le w hW)
    have hi : IsIntegralCut (expandedGraph G w) Y (demands w D) :=
      fun a b hab => hY a b (expanded_fractional hf hW a b hab)
    refine ⟨originalCut w Y, expanded_integral_pullback Y hi, ?_⟩
    calc
      _ ≤ (Y.card : ℝ≥0) := by exact_mod_cast originalCut_card_le w Y
      _ ≤ α * totalWeight (uniformWeight w) := hsize
      _ ≤ α * (2 * totalWeight w) :=
        mul_le_mul_of_nonneg_left (expanded_totalWeight_le w hW) zero_le
      _ = _ := by ring
  · have hz : totalWeight (preparedWeight w) = 0 := le_antisymm (le_of_not_gt hW) zero_le
    have hc : weightedCost (fun _ : TerminalPorts.Vertex V => 1) (preparedWeight w) = 0 := by
      rw [weightedCost_unit, hz]
    obtain ⟨Y, hY, hcost⟩ := UnitCostReduction.zero_cost_cut
      (TerminalPorts.graph G) (preparedWeight w) (fun _ => 1) hc
    have hi : IsIntegralCut (TerminalPorts.graph G) Y (TerminalPorts.demands D) :=
      fun a b hab => hY a b (prepared_fractional hf a b hab)
    refine ⟨TerminalPorts.corePreimage Y, (TerminalPorts.isIntegralCut_iff G Y D).mp hi, ?_⟩
    have hyzero : Y = ∅ := by
      rw [cutCost_unit] at hcost
      exact Finset.card_eq_zero.mp (by exact_mod_cast hcost)
    subst Y
    simp [TerminalPorts.corePreimage]

/-- The all-pairs threshold-cut specialization of the finite reduction. -/
theorem threshold_round_of_bounded_uniform_oracle (G : Digraph V) (w : V → ℝ≥0)
    (α : ℝ≥0)
    (oracle : BoundedUniformRoundingOracle.{u} (6 * Fintype.card V) (2 * totalWeight w) α) :
    ∃ X : Finset V, IsIntegralCut G X (thresholdDemands G w) ∧
      (X.card : ℝ≥0) ≤ 2 * α * totalWeight w :=
  round_of_bounded_uniform_oracle G w (thresholdDemands G w)
    (isFractionalCut_thresholdDemands G w) α oracle

end UniformWeightReduction
end
end DirectedFlowCutGap
