import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Tactic.Ring.Basic

/-!
# The finite-field incidence construction

The construction in Section 2.1 and Lemma 6 of Bodwin--Lopez,
*Unconditional Lower Bounds for Degree Fault Tolerant Spanners*,
arXiv:2607.07576v1.

Our dimension is `d + 2`, so the paper's parameter is `k = d + 2`.
The restriction `k ≥ 2` is essential for lines to be actual distinct subsets:
in dimension one all the vectors `(1,t,...,t^(k-1))` are `(1)`.
A line is represented uniquely by its slope parameter and its intercept in
the first-coordinate-zero hyperplane. `lineSet_injective` verifies that this
representation does not create duplicate, artificially labelled lines.
-/

namespace DegreeFaultSpanners

variable (F : Type*) (d : ℕ)

/-- Points in the paper's `k = d + 2` dimensional space. -/
abbrev Point := Fin (d + 2) → F

/-- A slope parameter and the remaining coordinates of the intercept. -/
abbrev Line := F × (Fin (d + 1) → F)

variable {F d} [Field F]

/-- The direction `(1,t,t²,...,t^(k-1))`. -/
def slope (t : F) : Point F d := fun i => t ^ (i : ℕ)

@[simp] theorem slope_zero (t : F) : slope (d := d) t 0 = 1 := by simp [slope]

@[simp] theorem slope_succ (t : F) (i : Fin (d + 1)) :
    slope (d := d) t i.succ = t ^ ((i : ℕ) + 1) := rfl

/-- Distinct parameters give distinct direction vectors when `k ≥ 2`. -/
theorem slope_injective : Function.Injective (slope (F := F) (d := d)) := by
  intro t u h
  have h₁ := congrFun h (0 : Fin (d + 1)).succ
  simpa [slope] using h₁

/-- Distinct slope parameters also give distinct projective directions. -/
theorem slope_smul_eq_iff (c t u : F) :
    c • slope (d := d) t = slope u ↔ c = 1 ∧ t = u := by
  constructor
  · intro h
    have hc : c = 1 := by simpa [smul_eq_mul] using congrFun h 0
    subst c
    exact ⟨rfl, slope_injective (by simpa using h)⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- The point on a canonical line with first coordinate `a`. -/
def linePoint (l : Line F d) (a : F) : Point F d :=
  Fin.cases a (fun i => l.2 i + a * l.1 ^ ((i : ℕ) + 1))

@[simp] theorem linePoint_zero (l : Line F d) (a : F) : linePoint l a 0 = a := rfl

@[simp] theorem linePoint_succ (l : Line F d) (a : F) (i : Fin (d + 1)) :
    linePoint l a i.succ = l.2 i + a * l.1 ^ ((i : ℕ) + 1) := rfl

/-- The actual subset of points belonging to the represented line. -/
def lineSet (l : Line F d) : Set (Point F d) := Set.range (linePoint l)

@[simp] theorem linePoint_mem (l : Line F d) (a : F) : linePoint l a ∈ lineSet l :=
  ⟨a, rfl⟩

theorem linePoint_injective (l : Line F d) : Function.Injective (linePoint l) := by
  intro a b h
  exact congrFun h 0

/-- Coordinate form of incidence: `xᵢ = bᵢ + x₀ tⁱ` for `i ≥ 1`. -/
theorem mem_lineSet_iff (l : Line F d) (x : Point F d) :
    x ∈ lineSet l ↔ ∀ i : Fin (d + 1), x i.succ = l.2 i + x 0 * l.1 ^ ((i : ℕ) + 1) := by
  constructor
  · rintro ⟨a, rfl⟩ i
    rfl
  · intro h
    refine ⟨x 0, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact (h j).symm

/-- The unique line of slope `t` through the point `x`. -/
def lineThrough (t : F) (x : Point F d) : Line F d :=
  (t, fun i => x i.succ - x 0 * t ^ ((i : ℕ) + 1))

@[simp] theorem lineThrough_slope (t : F) (x : Point F d) : (lineThrough t x).1 = t := rfl

@[simp] theorem mem_lineThrough (t : F) (x : Point F d) : x ∈ lineSet (lineThrough t x) := by
  rw [mem_lineSet_iff]
  intro i
  simp [lineThrough]

theorem eq_lineThrough_of_mem {l : Line F d} {x : Point F d} (h : x ∈ lineSet l) :
    l = lineThrough l.1 x := by
  apply Prod.ext
  · rfl
  funext i
  have hi := (mem_lineSet_iff l x).mp h i
  simp only [lineThrough]
  rw [hi]
  ring1

/-- Exactly one line of each slope passes through every point. -/
theorem existsUnique_line_through (t : F) (x : Point F d) :
    ∃! l : Line F d, l.1 = t ∧ x ∈ lineSet l := by
  refine ⟨lineThrough t x, ⟨rfl, mem_lineThrough t x⟩, ?_⟩
  intro l hl
  simpa [hl.1] using eq_lineThrough_of_mem hl.2

/-- Canonical line records inject into actual subsets of the point space. -/
theorem lineSet_injective : Function.Injective (lineSet (F := F) (d := d)) := by
  intro l m h
  have hzero : linePoint l 0 ∈ lineSet m := h ▸ linePoint_mem l 0
  have htail : l.2 = m.2 := by
    funext i
    simpa using (mem_lineSet_iff m (linePoint l 0)).mp hzero i
  have hone : linePoint l 1 ∈ lineSet m := h ▸ linePoint_mem l 1
  have hslope : l.1 = m.1 := by
    have hi := (mem_lineSet_iff m (linePoint l 1)).mp hone (0 : Fin (d + 1))
    simp only [linePoint_succ, linePoint_zero, Fin.val_zero, zero_add, pow_one, one_mul] at hi
    simpa [htail] using hi
  exact Prod.ext hslope htail

/-- A point on a line is determined by its first coordinate. -/
theorem linePoint_first_eq_of_mem {l : Line F d} {x : Point F d}
    (h : x ∈ lineSet l) : linePoint l (x 0) = x := by
  rcases h with ⟨a, rfl⟩
  rfl

/-- Two points on a line differ by a scalar multiple of its slope vector. -/
theorem sub_eq_smul_slope_of_mem {l : Line F d} {x y : Point F d}
    (hx : x ∈ lineSet l) (hy : y ∈ lineSet l) :
    y - x = (y 0 - x 0) • slope l.1 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [smul_eq_mul]
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, linePoint_succ,
      linePoint_zero, slope_succ]
    ring1

/-- Difference formula in the explicit affine parameters. -/
theorem linePoint_sub_linePoint (l : Line F d) (a b : F) :
    linePoint l a - linePoint l b = (a - b) • slope l.1 :=
  sub_eq_smul_slope_of_mem (linePoint_mem l b) (linePoint_mem l a)

/-- Distinct points on a line have distinct first coordinates. -/
theorem first_ne_of_ne_of_mem {l : Line F d} {x y : Point F d}
    (hx : x ∈ lineSet l) (hy : y ∈ lineSet l) (hne : x ≠ y) : x 0 ≠ y 0 := by
  intro h
  apply hne
  rw [← linePoint_first_eq_of_mem hx, ← linePoint_first_eq_of_mem hy, h]

/-- Intersecting lines with the same slope are the same line. -/
theorem eq_of_common_point_of_slope_eq {l m : Line F d} {x : Point F d}
    (hs : l.1 = m.1) (hl : x ∈ lineSet l) (hm : x ∈ lineSet m) : l = m := by
  calc
    l = lineThrough l.1 x := eq_lineThrough_of_mem hl
    _ = lineThrough m.1 x := congrArg (fun t => lineThrough t x) hs
    _ = m := (eq_lineThrough_of_mem hm).symm

/-- Parallel lines are distinct canonical lines with the same slope. -/
def Parallel (l m : Line F d) : Prop := l ≠ m ∧ l.1 = m.1

/-- Parallel lines are disjoint as actual subsets. -/
theorem Parallel.disjoint {l m : Line F d} (h : Parallel l m) :
    Disjoint (lineSet l) (lineSet m) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact h.1 (eq_of_common_point_of_slope_eq h.2 hx hy)

/-- The paper's noncanonical affine-line description. -/
def affineLine (x : Point F d) (t : F) : Set (Point F d) :=
  Set.range (fun a : F => x + a • slope t)

/-- A canonical line point is the usual affine parametrization. -/
theorem linePoint_eq_affine (l : Line F d) (a : F) :
    linePoint l a = linePoint l 0 + a • slope l.1 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [smul_eq_mul]
  · simp [smul_eq_mul]

/-- Every canonical line is a line in the manuscript's affine description. -/
theorem lineSet_eq_affineLine (l : Line F d) :
    lineSet l = affineLine (linePoint l 0) l.1 := by
  unfold lineSet affineLine
  congr 1
  funext a
  exact linePoint_eq_affine l a

/-- Changing the base point to its canonical intercept preserves the affine line. -/
theorem affineLine_eq_lineSet (x : Point F d) (t : F) :
    affineLine x t = lineSet (lineThrough t x) := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    rw [mem_lineSet_iff]
    intro i
    simp [lineThrough, smul_eq_mul]
    ring1
  · intro hy
    refine ⟨y 0 - x 0, ?_⟩
    have h := (mem_lineSet_iff (lineThrough t x) y).mp hy
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, slope_succ]
      rw [h j]
      simp only [lineThrough]
      ring1

/-- A step in direction `t` stays on the canonical line through its starting point. -/
theorem add_smul_mem_lineThrough (x : Point F d) (t a : F) :
    x + a • slope t ∈ lineSet (lineThrough t x) := by
  rw [← affineLine_eq_lineSet]
  exact ⟨a, rfl⟩

/-- Exact agreement with the paper's set of actual affine-line subsets. -/
theorem range_lineSet :
    Set.range (lineSet (F := F) (d := d)) =
      {s | ∃ x : Point F d, ∃ t : F, s = affineLine x t} := by
  ext s
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨linePoint l 0, l.1, lineSet_eq_affineLine l⟩
  · rintro ⟨x, t, rfl⟩
    exact ⟨lineThrough t x, (affineLine_eq_lineSet x t).symm⟩

/-- The affine parameter is a bijection with the points of a line. -/
def linePointEquiv (l : Line F d) : F ≃ lineSet l where
  toFun a := ⟨linePoint l a, linePoint_mem l a⟩
  invFun x := x.1 0
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    rcases x.2 with ⟨a, ha⟩
    simp [← ha]

variable (F d)

/-- The bipartite vertex type: points on the left and genuine canonical lines on the right. -/
abbrev Vertex := Point F d ⊕ Line F d

/-- The incidence graph from Section 2.1. -/
def incidenceGraph : SimpleGraph (Vertex F d) where
  Adj
    | Sum.inl x, Sum.inr l => x ∈ lineSet l
    | Sum.inr l, Sum.inl x => x ∈ lineSet l
    | _, _ => False
  symm := ⟨by
    intro v w h
    cases v <;> cases w <;> exact h⟩
  loopless := ⟨by
    intro v
    cases v <;> exact not_false⟩

@[simp] theorem incidenceGraph_inl_inr (x : Point F d) (l : Line F d) :
    (incidenceGraph F d).Adj (Sum.inl x) (Sum.inr l) ↔ x ∈ lineSet l := Iff.rfl

@[simp] theorem incidenceGraph_inr_inl (l : Line F d) (x : Point F d) :
    (incidenceGraph F d).Adj (Sum.inr l) (Sum.inl x) ↔ x ∈ lineSet l := Iff.rfl

@[simp] theorem incidenceGraph_not_inl_inl (x y : Point F d) :
    ¬ (incidenceGraph F d).Adj (Sum.inl x) (Sum.inl y) := not_false

@[simp] theorem incidenceGraph_not_inr_inr (l m : Line F d) :
    ¬ (incidenceGraph F d).Adj (Sum.inr l) (Sum.inr m) := not_false

/-- The two sides of the graph give an explicit bipartition. -/
theorem incidenceGraph_isBipartiteWith :
    (incidenceGraph F d).IsBipartiteWith
      (Set.range Sum.inl) (Set.range Sum.inr) where
  disjoint := by
    rw [Set.disjoint_left]
    rintro v ⟨x, rfl⟩ ⟨l, h⟩
    cases h
  mem_of_adj := by
    intro v w h
    cases v with
    | inl x =>
      cases w with
      | inl y => exact False.elim h
      | inr l => exact Or.inl ⟨⟨x, rfl⟩, ⟨l, rfl⟩⟩
    | inr l =>
      cases w with
      | inl x => exact Or.inr ⟨⟨l, rfl⟩, ⟨x, rfl⟩⟩
      | inr m => exact False.elim h

/-- The constructed simple graph is bipartite. -/
theorem incidenceGraph_isBipartite : (incidenceGraph F d).IsBipartite :=
  (incidenceGraph_isBipartiteWith F d).isBipartite

/-- Neighbors of a point are parametrized by the slope. -/
def pointNeighborEquiv (x : Point F d) :
    F ≃ (incidenceGraph F d).neighborSet (Sum.inl x) where
  toFun t := ⟨Sum.inr (lineThrough t x), mem_lineThrough t x⟩
  invFun n := match n.1 with
    | Sum.inl _ => 0
    | Sum.inr l => l.1
  left_inv _ := rfl
  right_inv n := by
    rcases n with ⟨v, hv⟩
    cases v with
    | inl y => exact False.elim hv
    | inr l =>
      apply Subtype.ext
      exact congrArg Sum.inr (eq_lineThrough_of_mem hv).symm

/-- Neighbors of a line are parametrized by the first coordinate. -/
def lineNeighborEquiv (l : Line F d) :
    F ≃ (incidenceGraph F d).neighborSet (Sum.inr l) where
  toFun a := ⟨Sum.inl (linePoint l a), linePoint_mem l a⟩
  invFun n := match n.1 with
    | Sum.inl x => x 0
    | Sum.inr _ => 0
  left_inv _ := rfl
  right_inv n := by
    rcases n with ⟨v, hv⟩
    cases v with
    | inl x =>
      apply Subtype.ext
      exact congrArg Sum.inl (linePoint_first_eq_of_mem hv)
    | inr m => exact False.elim hv

/-- An incidence edge is uniquely specified by its line and first coordinate. -/
def incidenceEdge (p : Line F d × F) : (incidenceGraph F d).edgeSet :=
  ⟨s(Sum.inl (linePoint p.1 p.2), Sum.inr p.1), linePoint_mem p.1 p.2⟩

theorem incidenceEdge_injective : Function.Injective (incidenceEdge F d) := by
  rintro ⟨l, a⟩ ⟨m, b⟩ h
  have he := congrArg Subtype.val h
  have hp : linePoint l a = linePoint m b ∧ l = m := by
    simpa only [incidenceEdge, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, false_and, or_false] using he
  obtain ⟨hpoint, rfl⟩ := hp
  exact Prod.ext rfl (linePoint_injective l hpoint)

theorem incidenceEdge_surjective : Function.Surjective (incidenceEdge F d) := by
  rintro ⟨e, he⟩
  revert he
  refine Sym2.inductionOn e ?_
  intro v w he
  cases v with
  | inl x =>
    cases w with
    | inl y => exact False.elim he
    | inr l =>
      rcases he with ⟨a, ha⟩
      refine ⟨(l, a), ?_⟩
      apply Subtype.ext
      change s(Sum.inl (linePoint l a), Sum.inr l) = s(Sum.inl x, Sum.inr l)
      rw [ha]
  | inr l =>
    cases w with
    | inl x =>
      rcases he with ⟨a, ha⟩
      refine ⟨(l, a), ?_⟩
      apply Subtype.ext
      change s(Sum.inl (linePoint l a), Sum.inr l) = s(Sum.inr l, Sum.inl x)
      rw [ha, Sym2.eq_swap]
    | inr m => exact False.elim he

/-- A genuine bijection, avoiding an assumption about double-counting edges. -/
noncomputable def incidenceEdgeEquiv :
    Line F d × F ≃ (incidenceGraph F d).edgeSet :=
  Equiv.ofBijective (incidenceEdge F d)
    ⟨incidenceEdge_injective F d, incidenceEdge_surjective F d⟩

section Counting

variable [Fintype F]

omit [Field F] in
/-- There are `p^k` points. -/
theorem card_point : Fintype.card (Point F d) = Fintype.card F ^ (d + 2) := by
  simp [Point]

omit [Field F] in
/-- There are `p^k` distinct lines. -/
theorem card_line : Fintype.card (Line F d) = Fintype.card F ^ (d + 2) := by
  simp [Line, pow_succ, mul_comm]

/-- Each line contains exactly `p` points. -/
theorem card_lineSet (l : Line F d) : Nat.card (lineSet l) = Fintype.card F := by
  rw [← Nat.card_congr (linePointEquiv l), Nat.card_eq_fintype_card]

omit [Field F] in
/-- Lemma 6, vertex count: `2p^k`. -/
theorem card_vertex : Fintype.card (Vertex F d) = 2 * Fintype.card F ^ (d + 2) := by
  rw [Fintype.card_sum, card_point, card_line]
  omega

/-- Counting actual subsets gives the same number as counting canonical records. -/
theorem card_actualLines :
    Nat.card (Set.range (lineSet (F := F) (d := d))) = Fintype.card F ^ (d + 2) := by
  rw [← Nat.card_congr (Equiv.ofInjective (lineSet (F := F) (d := d)) lineSet_injective), Nat.card_eq_fintype_card]
  exact card_line F d

/-- Lemma 6, edge count: `p^(k+1)` for the undirected simple graph. -/
theorem card_edgeSet :
    Nat.card (incidenceGraph F d).edgeSet = Fintype.card F ^ (d + 3) := by
  rw [← Nat.card_congr (incidenceEdgeEquiv F d), Nat.card_eq_fintype_card,
    Fintype.card_prod, card_line]
  exact (pow_succ (Fintype.card F) (d + 2)).symm

/-- Every point and every line has exactly `p` neighbors. -/
theorem card_neighborSet (v : Vertex F d) :
    Nat.card ((incidenceGraph F d).neighborSet v) = Fintype.card F := by
  cases v with
  | inl x => rw [← Nat.card_congr (pointNeighborEquiv F d x), Nat.card_eq_fintype_card]
  | inr l => rw [← Nat.card_congr (lineNeighborEquiv F d l), Nat.card_eq_fintype_card]

/-- Lemma 6 with the manuscript's dimension parameter `k ≥ 2`.

The finite-field size is `p = Fintype.card F`, and the paper's `n` is `p^k`.
Thus the two conclusions are precisely `2n` vertices and `p^(k+1)` edges.
-/
theorem lemma6_size (k : ℕ) (hk : 2 ≤ k) :
    Fintype.card (Vertex F (k - 2)) = 2 * Fintype.card F ^ k ∧
      Nat.card (incidenceGraph F (k - 2)).edgeSet = Fintype.card F ^ (k + 1) := by
  have h₂ : k - 2 + 2 = k := Nat.sub_add_cancel hk
  have h₃ : k - 2 + 3 = k + 1 := by omega
  exact ⟨by rw [card_vertex, h₂], by rw [card_edgeSet, h₃]⟩

end Counting

end DegreeFaultSpanners
