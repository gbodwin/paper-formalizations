import DegreeFaultSpanners.ShortReach
import DegreeFaultSpanners.GeometryWalk
import Mathlib.Tactic.Abel

/-!
# Graph realization of short transverse reachability

This file closes the distinction between the algebraic predicate `ShortReach`
and the manuscript's genuine simple paths. It also proves the path-straightening
step of Lemma 12: a point-to-point incidence walk can be replaced by a simple
path with at most twice as many edges as distinct slopes used by the walk.

All restrictions below delete incident edges of forbidden line vertices. Keeping
those vertices as isolated vertices does not change point-to-point paths.
-/

namespace DegreeFaultSpanners

open scoped BigOperators

variable {F : Type*} [Field F] {d : ℕ}

/-- The incidence graph with only lines whose slopes satisfy `allowed`. -/
def slopeRestrictedGraph (allowed : F → Prop) : SimpleGraph (Vertex F d) where
  Adj
    | Sum.inl x, Sum.inr l => x ∈ lineSet l ∧ allowed l.1
    | Sum.inr l, Sum.inl x => x ∈ lineSet l ∧ allowed l.1
    | _, _ => False
  symm := ⟨by intro v w h; cases v <;> cases w <;> exact h⟩
  loopless := ⟨by intro v; cases v <;> exact not_false⟩

/-- Delete all edges incident to a line of the designated slope. -/
def transverseGraph (t : F) : SimpleGraph (Vertex F d) :=
  slopeRestrictedGraph (fun s => s ≠ t)

@[simp] theorem transverseGraph_inl_inr (t : F) (x : Point F d) (l : Line F d) :
    (transverseGraph (d := d) t).Adj (Sum.inl x) (Sum.inr l) ↔
      x ∈ lineSet l ∧ l.1 ≠ t := Iff.rfl

@[simp] theorem transverseGraph_inr_inl (t : F) (l : Line F d) (x : Point F d) :
    (transverseGraph (d := d) t).Adj (Sum.inr l) (Sum.inl x) ↔
      x ∈ lineSet l ∧ l.1 ≠ t := Iff.rfl

theorem slopeRestrictedGraph_le (allowed : F → Prop) :
    slopeRestrictedGraph (d := d) allowed ≤ incidenceGraph F d := by
  intro v w h
  cases v <;> cases w
  · exact h
  · exact h.1
  · exact h.1
  · exact h

theorem transverseGraph_le (t : F) :
    transverseGraph (d := d) t ≤ incidenceGraph F d := slopeRestrictedGraph_le _

/-- A finite linear combination is an actual alternating walk of twice the
support size, including when one or more coefficients vanish. -/
theorem exists_walk_of_sum (allowed : F → Prop) (S : Finset F) (c : F → F)
    (hS : ∀ s ∈ S, allowed s) (a : Point F d) :
    ∃ p : (slopeRestrictedGraph (d := d) allowed).Walk (Sum.inl a)
      (Sum.inl (a + ∑ s ∈ S, c s • momentCurve (d + 2) s)),
      p.length ≤ 2 * S.card := by
  classical
  revert hS
  induction S using Finset.induction_on generalizing a with
  | empty =>
    intro _
    have hend : a + ∑ s ∈ (∅ : Finset F), c s • momentCurve (d + 2) s = a := by simp
    let q := (SimpleGraph.Walk.nil :
      (slopeRestrictedGraph (d := d) allowed).Walk (Sum.inl a) (Sum.inl a)).copy
        rfl (congrArg Sum.inl hend.symm)
    refine ⟨q, ?_⟩
    simp only [q, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_nil,
      Finset.card_empty, mul_zero, Nat.le_refl]
  | @insert s S hs ih =>
    intro hS
    have hsallowed := hS s (Finset.mem_insert_self s S)
    have hSallowed : ∀ u ∈ S, allowed u := fun u hu => hS u (Finset.mem_insert_of_mem hu)
    obtain ⟨p, hp⟩ := ih (a + c s • momentCurve (d + 2) s) hSallowed
    rw [Finset.sum_insert hs, ← add_assoc]
    let q : (slopeRestrictedGraph (d := d) allowed).Walk (Sum.inl a)
        (Sum.inl (a + c s • momentCurve (d + 2) s)) :=
      .cons (v := Sum.inr (lineThrough s a))
        (show a ∈ lineSet (lineThrough s a) ∧ allowed s from
        ⟨mem_lineThrough s a, hsallowed⟩)
        (.cons (v := Sum.inl (a + c s • momentCurve (d + 2) s))
          (show a + c s • momentCurve (d + 2) s ∈ lineSet (lineThrough s a) ∧
            allowed s from ⟨add_smul_mem_lineThrough a s (c s), hsallowed⟩) .nil)
    refine ⟨q.append p, ?_⟩
    have hq : q.length = 2 := rfl
    rw [SimpleGraph.Walk.length_append, hq, Finset.card_insert_of_notMem hs]
    omega

/-- Loop erasure realizes a sparse displacement by a genuine simple path. -/
theorem exists_path_of_sparseCombination (allowed : F → Prop)
    (S : Finset F) (c : F → F) (hS : ∀ s ∈ S, allowed s)
    {a b : Point F d} (hcomb : SparseCombination (d + 2) S c (b - a)) :
    ∃ p : (slopeRestrictedGraph (d := d) allowed).Walk (Sum.inl a) (Sum.inl b),
      p.IsPath ∧ p.length ≤ 2 * S.card := by
  classical
  obtain ⟨p, hp⟩ := exists_walk_of_sum allowed S c hS a
  have hend : a + ∑ s ∈ S, c s • momentCurve (d + 2) s = b := by
    rw [← hcomb]
    abel
  let q := p.copy rfl (congrArg Sum.inl hend)
  refine ⟨q.bypass, q.bypass_isPath, q.length_bypass_le_length.trans ?_⟩
  simpa only [q, SimpleGraph.Walk.length_copy] using hp

namespace IncidenceWalkEncoding

variable {a b : Point F d}
    {p : (incidenceGraph F d).Walk (Sum.inl a) (Sum.inl b)}

/-- The finite set of distinct slopes actually occurring in the encoding. -/
noncomputable def slopeSet (e : IncidenceWalkEncoding p) : Finset F := by
  classical
  exact Finset.univ.image (fun i => (e.lines i).1)

/-- Aggregate the affine displacement coefficients of equal slopes. -/
noncomputable def slopeCoefficient (e : IncidenceWalkEncoding p) (s : F) : F := by
  classical
  exact ∑ i ∈ Finset.univ.filter (fun i => (e.lines i).1 = s),
    (e.points i.succ 0 - e.points i.castSucc 0)

/-- Telescoping an actual walk, followed by grouping equal slopes. -/
theorem sparseCombination (e : IncidenceWalkEncoding p) :
    SparseCombination (d + 2) e.slopeSet e.slopeCoefficient (b - a) := by
  classical
  unfold SparseCombination
  funext q
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, momentCurve]
  calc
    b q - a q = ∑ i : Fin e.halfLength,
        (e.points i.succ q - e.points i.castSucc q) := by
      simpa only [e.first_point, e.last_point] using
        (sum_fin_successive_sub (fun i => e.points i q)).symm
    _ = ∑ i : Fin e.halfLength,
        (e.points i.succ 0 - e.points i.castSucc 0) * (e.lines i).1 ^ (q : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrFun (sub_eq_smul_slope_of_mem (e.from_mem i) (e.to_mem i)) q
    _ = ∑ s ∈ e.slopeSet, ∑ i ∈ Finset.univ.filter (fun i => (e.lines i).1 = s),
        (e.points i.succ 0 - e.points i.castSucc 0) * (e.lines i).1 ^ (q : ℕ) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun i _ => Finset.mem_image_of_mem (fun j => (e.lines j).1) (Finset.mem_univ i)) _
    _ = ∑ s ∈ e.slopeSet, e.slopeCoefficient s * s ^ (q : ℕ) := by
      apply Finset.sum_congr rfl
      intro s _
      unfold slopeCoefficient
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]

theorem card_slopeSet_le (e : IncidenceWalkEncoding p) :
    e.slopeSet.card ≤ e.halfLength := by
  classical
  exact (Finset.card_image_le).trans_eq (Finset.card_fin e.halfLength)

end IncidenceWalkEncoding

/-- Every encoded line of a slope-restricted walk has an allowed slope. -/
theorem encoding_lines_allowed (allowed : F → Prop) {a b : Point F d}
    (p : (slopeRestrictedGraph (d := d) allowed).Walk (Sum.inl a) (Sum.inl b))
    (e : IncidenceWalkEncoding (p.mapLe (slopeRestrictedGraph_le allowed)))
    (i : Fin e.halfLength) : allowed (e.lines i).1 := by
  have hlen : p.length = 2 * e.halfLength := by
    simpa using e.length_eq
  have h := p.adj_getVert_succ (i := 2 * i.val) (by omega)
  have hfrom : p.getVert (2 * i.val) = Sum.inl (e.points i.castSucc) := by
    simpa using e.get_even i.castSucc
  have hto : p.getVert (2 * i.val + 1) = Sum.inr (e.lines i) := by
    simpa using e.get_odd i
  rw [hfrom, hto] at h
  exact h.2

/-- A restricted walk supplies a sparse witness supported on its actual slopes. -/
theorem exists_sparseCombination_of_walk (allowed : F → Prop) {a b : Point F d}
    (p : (slopeRestrictedGraph (d := d) allowed).Walk (Sum.inl a) (Sum.inl b)) :
    ∃ (S : Finset F) (c : F → F),
      (∀ s ∈ S, allowed s) ∧ 2 * S.card ≤ p.length ∧
        SparseCombination (d + 2) S c (b - a) := by
  classical
  let e := incidenceWalkEncoding (p.mapLe (slopeRestrictedGraph_le allowed))
  refine ⟨e.slopeSet, e.slopeCoefficient, ?_, ?_, e.sparseCombination⟩
  · intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact encoding_lines_allowed allowed p e i
  · have hcard := e.card_slopeSet_le
    have hlen : p.length = 2 * e.halfLength := by simpa using e.length_eq
    omega

/-- `ShortReach` is equivalent to an actual short simple path after all lines
of the designated slope are removed. The edge-length cutoff is exactly the
paper's line-length cutoff `2 * (r + 1) ≤ d + 2`. -/
theorem shortReach_iff_exists_transverse_path (t : F) (a b : Point F d) :
    ShortReach (d + 2) t a b ↔
      ∃ p : (transverseGraph (d := d) t).Walk (Sum.inl a) (Sum.inl b),
        p.IsPath ∧ p.length + 2 ≤ d + 2 := by
  unfold transverseGraph
  constructor
  · rintro ⟨S, c, ht, hcard, hcomb⟩
    have hallowed : ∀ s ∈ S, s ≠ t := by
      intro s hs hst
      subst s
      exact ht hs
    obtain ⟨p, hp, hlen⟩ := exists_path_of_sparseCombination (fun s => s ≠ t)
      S c hallowed hcomb
    exact ⟨p, hp, by omega⟩
  · rintro ⟨p, _, hlen⟩
    obtain ⟨S, c, hallowed, hcard, hcomb⟩ :=
      exists_sparseCombination_of_walk (fun s => s ≠ t) p
    exact ⟨S, c, fun ht => hallowed t ht rfl, by omega, hcomb⟩

/-- Equivalent formulation explicitly counting the alternating line vertices. -/
theorem shortReach_iff_exists_transverse_path_halfLength (t : F) (a b : Point F d) :
    ShortReach (d + 2) t a b ↔
      ∃ (p : (transverseGraph (d := d) t).Walk (Sum.inl a) (Sum.inl b)) (r : ℕ),
        p.IsPath ∧ p.length = 2 * r ∧ 2 * (r + 1) ≤ d + 2 := by
  rw [shortReach_iff_exists_transverse_path]
  constructor
  · rintro ⟨p, hp, hlen⟩
    have heven := incidence_walk_length_eq_twice_half (p.mapLe (transverseGraph_le t))
    simp only [SimpleGraph.Walk.length_map] at heven
    exact ⟨p, p.length / 2, hp, heven, by omega⟩
  · rintro ⟨p, r, hp, heven, hlen⟩
    exact ⟨p, hp, by omega⟩

/-- Lemma 12 in a stronger slope-preserving form. The replacement is simple,
uses only slopes already appearing in the original walk, and has at most
`2 * number_of_distinct_slopes` graph edges. -/
theorem incidence_walk_straightening {a b : Point F d}
    (p : (incidenceGraph F d).Walk (Sum.inl a) (Sum.inl b)) :
    ∃ q : (slopeRestrictedGraph (d := d)
        (fun s => s ∈ (incidenceWalkEncoding p).slopeSet)).Walk (Sum.inl a) (Sum.inl b),
      q.IsPath ∧ q.length ≤ 2 * (incidenceWalkEncoding p).slopeSet.card := by
  exact exists_path_of_sparseCombination _ _ _ (fun _ hs => hs)
    (incidenceWalkEncoding p).sparseCombination

/-- Lemma 12 with any permitted family of slopes, stated in the same restricted
incidence graph as the original walk. -/
theorem restricted_walk_straightening (allowed : F → Prop) {a b : Point F d}
    (p : (slopeRestrictedGraph (d := d) allowed).Walk (Sum.inl a) (Sum.inl b)) :
    ∃ q : (slopeRestrictedGraph (d := d) allowed).Walk (Sum.inl a) (Sum.inl b),
      q.IsPath ∧ q.length ≤
        2 * (incidenceWalkEncoding (p.mapLe (slopeRestrictedGraph_le allowed))).slopeSet.card := by
  classical
  let e := incidenceWalkEncoding (p.mapLe (slopeRestrictedGraph_le allowed))
  apply exists_path_of_sparseCombination allowed e.slopeSet e.slopeCoefficient
    ?_ e.sparseCombination
  intro s hs
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
  exact encoding_lines_allowed allowed p e i

/-- The manuscript's transverse form of Lemma 12, including zero-length paths. -/
theorem transverse_walk_straightening (t : F) {a b : Point F d}
    (p : (transverseGraph (d := d) t).Walk (Sum.inl a) (Sum.inl b)) :
    ∃ q : (transverseGraph (d := d) t).Walk (Sum.inl a) (Sum.inl b),
      q.IsPath ∧ q.length ≤
        2 * (incidenceWalkEncoding (p.mapLe (transverseGraph_le t))).slopeSet.card :=
  restricted_walk_straightening (fun s => s ≠ t) p

/-- The algebraic failure relation is exactly the graph-path failure relation. -/
theorem shortFailure_iff_transverse_path {a b : Point F d} {l m : Line F d} :
    shortFailure a l b m ↔
      m ≠ l ∧ m.1 = l.1 ∧ b ∈ lineSet m ∧
        ∃ p : (transverseGraph (d := d) l.1).Walk (Sum.inl a) (Sum.inl b),
          p.IsPath ∧ p.length + 2 ≤ d + 2 := by
  unfold shortFailure
  rw [shortReach_iff_exists_transverse_path]

end DegreeFaultSpanners
