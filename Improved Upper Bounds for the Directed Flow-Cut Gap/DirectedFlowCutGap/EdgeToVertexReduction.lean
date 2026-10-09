import DirectedFlowCutGap.EdgeModel
import DirectedFlowCutGap.DyadicEdgeWeights

/-!
# Finite directed edge-to-vertex reduction

Concrete left/right label vertices and zero-weight endpoint ports. Inactive
labels are removed. The path projection below erases loops while retaining
actual original edges, rather than merely retaining original vertices.
The result is a finite oracle reduction, not a running-time or main-gap bound.
-/

namespace DirectedFlowCutGap
namespace EdgeToVertex

noncomputable section
open scoped BigOperators NNReal ENNReal
attribute [local instance] Classical.propDecidable

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {L : Type} [Fintype L] [DecidableEq L]

/-- The first summand consists of endpoint ports; the second of label vertices.
`false` denotes the left/end side, `true` the right/start side. -/
abbrev RawNode (V : Type u) (L : Type) := (V × Bool) ⊕ (V × Bool × L)

def start (v : V) : RawNode V L := .inl (v, true)
def finish (v : V) : RawNode V L := .inl (v, false)
def right (label : V × V → L) (e : V × V) : RawNode V L :=
  .inr (e.1, true, label e)
def left (label : V × V → L) (e : V × V) : RawNode V L :=
  .inr (e.2, false, label e)

def base : RawNode V L → V
  | .inl x => x.1
  | .inr x => x.1

/-- Exactly the endpoint ports and labels incident to a mapped original edge. -/
def Active (G : Digraph V) (label : V × V → L) (x : RawNode V L) : Prop :=
  (∃ v b, x = .inl (v, b)) ∨
    ∃ e ∈ graphEdges G, x = right label e ∨ x = left label e

abbrev Node (G : Digraph V) (label : V × V → L) :=
  {x : RawNode V L // Active G label x}

omit [DecidableEq V] [Fintype L] [DecidableEq L] in
@[simp] theorem active_start (G : Digraph V) (label : V × V → L) (v : V) :
    Active G label (start v) := Or.inl ⟨v, true, rfl⟩
omit [DecidableEq V] [Fintype L] [DecidableEq L] in
@[simp] theorem active_finish (G : Digraph V) (label : V × V → L) (v : V) :
    Active G label (finish v) := Or.inl ⟨v, false, rfl⟩
omit [DecidableEq V] [Fintype L] [DecidableEq L] in
theorem active_right (G : Digraph V) (label : V × V → L) {e : V × V}
    (he : e ∈ graphEdges G) : Active G label (right label e) :=
  Or.inr ⟨e, he, Or.inl rfl⟩
omit [DecidableEq V] [Fintype L] [DecidableEq L] in
theorem active_left (G : Digraph V) (label : V × V → L) {e : V × V}
    (he : e ∈ graphEdges G) : Active G label (left label e) :=
  Or.inr ⟨e, he, Or.inr rfl⟩

def source (G : Digraph V) (label : V × V → L) (v : V) : Node G label :=
  ⟨start v, active_start G label v⟩
def target (G : Digraph V) (label : V × V → L) (v : V) : Node G label :=
  ⟨finish v, active_finish G label v⟩

/-- The directed biclique, endpoint ports, and original mapped edges. The
zero-weight source-to-end edge at each vertex also represents the empty walk. -/
def RawAdj (G : Digraph V) (label : V × V → L) : RawNode V L → RawNode V L → Prop
  | .inl (u, true), .inl (v, false) => u = v
  | .inl (u, true), .inr (v, true, _) => u = v
  | .inr (u, false, _), .inl (v, false) => u = v
  | .inr (u, false, _), .inr (v, true, _) => u = v
  | .inr (u, true, i), .inr (v, false, j) =>
      G.Adj u v ∧ label (u, v) = i ∧ label (u, v) = j
  | _, _ => False

def graph (G : Digraph V) (label : V × V → L) : Digraph (Node G label) where
  Adj x y := RawAdj G label x.val y.val

def rawWeight (G : Digraph V) (label : V × V → L) (value : L → ℝ≥0)
    (x : RawNode V L) : ℝ≥0 :=
  if Active G label x then match x with
    | .inl _ => 0
    | .inr (_, _, i) => value i
  else 0

def weight (G : Digraph V) (label : V × V → L) (value : L → ℝ≥0)
    (x : Node G label) : ℝ≥0 := rawWeight G label value x.val

/-- Each original edge contributes its cost to both mapped endpoint labels. -/
def rawCost (G : Digraph V) (label : V × V → L) (c : V × V → ℝ≥0)
    (x : RawNode V L) : ℝ≥0 :=
  ∑ e ∈ graphEdges G,
    ((if x = right label e then c e else 0) +
      (if x = left label e then c e else 0))

def cost (G : Digraph V) (label : V × V → L) (c : V × V → ℝ≥0)
    (x : Node G label) : ℝ≥0 := rawCost G label c x.val

omit [DecidableEq V] [Fintype L] [DecidableEq L] in
@[simp] theorem rawWeight_start (G : Digraph V) (label : V × V → L)
    (value : L → ℝ≥0) (v : V) : rawWeight G label value (start v) = 0 := by
  simp [rawWeight, start, Active]
omit [DecidableEq V] [Fintype L] [DecidableEq L] in
@[simp] theorem rawWeight_finish (G : Digraph V) (label : V × V → L)
    (value : L → ℝ≥0) (v : V) : rawWeight G label value (finish v) = 0 := by
  simp [rawWeight, finish, Active]
omit [DecidableEq V] [Fintype L] [DecidableEq L] in
@[simp] theorem rawWeight_right (G : Digraph V) (label : V × V → L)
    (value : L → ℝ≥0) {e : V × V} (he : e ∈ graphEdges G) :
    rawWeight G label value (right label e) = value (label e) := by
  simp only [rawWeight, active_right G label he, ↓reduceIte]
  rfl
omit [DecidableEq V] [Fintype L] [DecidableEq L] in
@[simp] theorem rawWeight_left (G : Digraph V) (label : V × V → L)
    (value : L → ℝ≥0) {e : V × V} (he : e ∈ graphEdges G) :
    rawWeight G label value (left label e) = value (label e) := by
  simp only [rawWeight, active_left G label he, ↓reduceIte]
  rfl

omit [Fintype L] in
@[simp] theorem rawCost_start (G : Digraph V) (label : V × V → L)
    (c : V × V → ℝ≥0) (v : V) : rawCost G label c (start v) = 0 := by
  simp [rawCost, start, right, left]
omit [Fintype L] in
@[simp] theorem rawCost_finish (G : Digraph V) (label : V × V → L)
    (c : V × V → ℝ≥0) (v : V) : rawCost G label c (finish v) = 0 := by
  simp [rawCost, finish, right, left]

omit [Fintype L] in
theorem rawCost_inactive (G : Digraph V) (label : V × V → L)
    (c : V × V → ℝ≥0) {x : RawNode V L} (hx : ¬Active G label x) :
    rawCost G label c x = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  have hr : x ≠ right label e := fun h => hx (h.symm ▸ active_right G label he)
  have hl : x ≠ left label e := fun h => hx (h.symm ▸ active_left G label he)
  simp [hr, hl]

omit [DecidableEq V] [DecidableEq L] in
/-- This is the actual cardinality after inactive-label removal. -/
theorem card_node_le (G : Digraph V) (label : V × V → L) :
    Fintype.card (Node G label) ≤ 2 * Fintype.card V * (Fintype.card L + 1) := by
  calc
    Fintype.card (Node G label) ≤ Fintype.card (RawNode V L) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = _ := by simp [RawNode, Fintype.card_sum, Fintype.card_prod]; ring

/-- The original edge set charged by a selected set of gadget nodes. -/
def pullback (G : Digraph V) (label : V × V → L) (Y : Finset (Node G label)) :
    Finset (V × V) :=
  (graphEdges G).filter fun e =>
    right label e ∈ Y.image Subtype.val ∨ left label e ∈ Y.image Subtype.val

omit [Fintype L] in
@[simp] theorem mem_pullback (G : Digraph V) (label : V × V → L)
    (Y : Finset (Node G label)) (e : V × V) :
    e ∈ pullback G label Y ↔ e ∈ graphEdges G ∧
      (right label e ∈ Y.image Subtype.val ∨ left label e ∈ Y.image Subtype.val) := by
  simp [pullback]

omit [DecidableEq V] [DecidableEq L] in
/-- Summing over the actual vertex type discards precisely the inactive zeros. -/
theorem sum_nodes_eq_raw (G : Digraph V) (label : V × V → L)
    (f : RawNode V L → ℝ≥0) (hf : ∀ x, ¬Active G label x → f x = 0) :
    (∑ x : Node G label, f x.val) = ∑ x : RawNode V L, f x := by
  rw [← Finset.sum_subtype (Finset.univ.filter (Active G label)) (by simp) f]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hx
  exact hf x (by simpa using hx)

/-- Exact finite incidence accounting, retaining arbitrary zero edge costs. -/
theorem sum_rawCost_mul (G : Digraph V) (label : V × V → L)
    (c : V × V → ℝ≥0) (f : RawNode V L → ℝ≥0) :
    (∑ x, rawCost G label c x * f x) =
      ∑ e ∈ graphEdges G, c e * (f (right label e) + f (left label e)) := by
  simp only [rawCost, Finset.sum_mul, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [Finset.sum_add_distrib, mul_add]

theorem weightedCost_eq (G : Digraph V) (label : V × V → L)
    (value : L → ℝ≥0) (c : V × V → ℝ≥0) :
    weightedCost (cost G label c) (weight G label value) =
      2 * weightedEdgeCost G c (value ∘ label) := by
  unfold weightedCost cost weight
  rw [sum_nodes_eq_raw G label
    (fun x => rawCost G label c x * rawWeight G label value x) (fun x hx => by
    rw [rawCost_inactive G label c hx, zero_mul])]
  rw [sum_rawCost_mul]
  unfold weightedEdgeCost
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [rawWeight_right G label value he, rawWeight_left G label value he]
  simp only [Function.comp_apply]
  ring

theorem sum_rawCost (G : Digraph V) (label : V × V → L) (c : V × V → ℝ≥0) :
    (∑ x, rawCost G label c x) = 2 * ∑ e ∈ graphEdges G, c e := by
  have h := sum_rawCost_mul G label c (fun _ => 1)
  calc
    (∑ x, rawCost G label c x) = ∑ e ∈ graphEdges G, c e * (1 + 1) := by
      simpa only [mul_one] using h
    _ = 2 * ∑ e ∈ graphEdges G, c e := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring

omit [Fintype L] in
theorem rawWeight_le_incidence (G : Digraph V) (label : V × V → L)
    (value : L → ℝ≥0) (x : RawNode V L) :
    rawWeight G label value x ≤ rawCost G label (value ∘ label) x := by
  by_cases hx : Active G label x
  · rcases hx with ⟨v, b, rfl⟩ | ⟨e, he, rfl | rfl⟩
    · simp [rawWeight]
    · rw [rawWeight_right G label value he]
      apply le_trans _ (Finset.single_le_sum (fun _ _ => bot_le) he)
      simp only [Function.comp_apply]
      exact le_add_of_nonneg_right bot_le
    · rw [rawWeight_left G label value he]
      apply le_trans _ (Finset.single_le_sum (fun _ _ => bot_le) he)
      simp only [Function.comp_apply]
      exact le_add_of_nonneg_left bot_le
  · simp [rawWeight, hx]

theorem totalWeight_le (G : Digraph V) (label : V × V → L)
    (value : L → ℝ≥0) :
    totalWeight (weight G label value) ≤ 2 * totalEdgeWeight G (value ∘ label) := by
  unfold totalWeight weight
  rw [sum_nodes_eq_raw G label _ (fun x hx => by simp [rawWeight, hx])]
  calc
    (∑ x, rawWeight G label value x) ≤ ∑ x, rawCost G label (value ∘ label) x :=
      Finset.sum_le_sum fun x _ => rawWeight_le_incidence G label value x
    _ = _ := sum_rawCost G label (value ∘ label)

omit [Fintype L] in
/-- Pulling back a vertex cut never increases its cost, even when both mapped
endpoints of the same edge were selected. -/
theorem pullback_cost_le (G : Digraph V) (label : V × V → L)
    (c : V × V → ℝ≥0) (Y : Finset (Node G label)) :
    edgeCutCost G c (pullback G label Y) ≤ cutCost (cost G label c) Y := by
  have hactual : (pullback G label Y).filter (fun e => G.Adj e.1 e.2) =
      pullback G label Y := by
    apply Finset.filter_eq_self.mpr
    intro e he
    exact (mem_graphEdges G e).mp ((mem_pullback G label Y e).mp he).1
  have hsum : cutCost (cost G label c) Y =
      ∑ e ∈ graphEdges G,
        ((if right label e ∈ Y.image Subtype.val then c e else 0) +
          (if left label e ∈ Y.image Subtype.val then c e else 0)) := by
    unfold cutCost cost
    rw [← Finset.sum_image (f := rawCost G label c)
      (fun _ _ _ _ h => Subtype.val_injective h)]
    simp only [rawCost]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    simp [Finset.sum_add_distrib]
  rw [hsum, edgeCutCost, hactual, pullback, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro e _
  by_cases hr : right label e ∈ Y.image Subtype.val <;>
    by_cases hl : left label e ∈ Y.image Subtype.val <;> simp [hr, hl]

omit [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L] in
/-- Every gadget arc is either internal to one original vertex or is precisely
one mapped original edge, with both of its specified label endpoints. -/
theorem rawAdj_cases (G : Digraph V) (label : V × V → L)
    {x y : RawNode V L} (h : RawAdj G label x y) :
    base x = base y ∨ (G.Adj (base x) (base y) ∧
      x = right label (base x, base y) ∧ y = left label (base x, base y)) := by
  rcases x with ⟨u, b⟩ | ⟨u, b, i⟩ <;>
    rcases y with ⟨v, d⟩ | ⟨v, d, j⟩ <;>
    cases b <;> cases d <;>
    simp_all [RawAdj, base, right, left]
  exact Or.inr (h.2.2.symm.trans h.2.1)

omit [Fintype V] [DecidableEq V] in
/-- Projection contracts internal gadget arcs and retains the actual original
edge on each nontrivial projected step. -/
theorem project_walk {U : Type*} [DecidableEq U] {H : Digraph U}
    (f : U → V) (K : Digraph V)
    (h : ∀ x y, H.Adj x y → f x = f y ∨ K.Adj (f x) (f y))
    {a b : U} (q : DirectedWalk H a b) : Nonempty (DirectedWalk K (f a) (f b)) := by
  induction q with
  | refl a => exact ⟨.refl (f a)⟩
  | @cons a u b ha q ih =>
    obtain ⟨r⟩ := ih
    rcases h a u ha with he | he
    · simpa only [he] using (show Nonempty (DirectedWalk K (f u) (f b)) from ⟨r⟩)
    · exact ⟨.cons he r⟩

/-- Only original edges whose two mapped labels occur internally are retained. -/
def representedEdges (G : Digraph V) (label : V × V → L) {s t : V}
    (p : SimplePath (graph G label) (source G label s) (target G label t)) :
    Finset (V × V) :=
  (graphEdges G).filter fun e =>
    right label e ∈ p.internalVertices.image Subtype.val ∧
      left label e ∈ p.internalVertices.image Subtype.val

omit [Fintype L] in
theorem internal_of_label (G : Digraph V) (label : V × V → L) {s t : V}
    (p : SimplePath (graph G label) (source G label s) (target G label t))
    (x : Node G label) (a : V × Bool × L) (hx : x.val = .inr a)
    (hm : x ∈ p.vertices) : x ∈ p.internalVertices := by
  apply Finset.mem_sdiff.mpr
  refine ⟨hm, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor <;> intro h <;>
    have hh := congrArg Subtype.val h <;> rw [hx] at hh <;>
    simp [source, target, start, finish] at hh

omit [Fintype L] in
theorem represented_of_path_edge (G : Digraph V) (label : V × V → L) {s t : V}
    (p : SimplePath (graph G label) (source G label s) (target G label t))
    {x y : Node G label} (hxy : (x, y) ∈ p.edges)
    (h : G.Adj (base x.val) (base y.val))
    (hx : x.val = right label (base x.val, base y.val))
    (hy : y.val = left label (base x.val, base y.val)) :
    (base x.val, base y.val) ∈ representedEdges G label p := by
  obtain ⟨i, hi⟩ := (p.mem_edges _).mp hxy
  have hxm : x ∈ p.vertices := by
    apply (p.mem_vertices _).mpr
    exact ⟨i.castSucc, congrArg Prod.fst hi⟩
  have hym : y ∈ p.vertices := by
    apply (p.mem_vertices _).mpr
    exact ⟨i.succ, congrArg Prod.snd hi⟩
  apply Finset.mem_filter.mpr
  refine ⟨(mem_graphEdges G _).mpr h, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨x, internal_of_label G label p x _ hx hxm, hx⟩
  · exact Finset.mem_image.mpr ⟨y, internal_of_label G label p y _ hy hym, hy⟩

omit [Fintype L] in
/-- Genuine edge-preserving projection of any actual gadget path. Erasing
original loops is performed in the graph restricted to represented edges. -/
theorem exists_projected_path (G : Digraph V) (label : V × V → L) {s t : V}
    (p : SimplePath (graph G label) (source G label s) (target G label t)) :
    ∃ q : SimplePath G s t, q.edges ⊆ representedEdges G label p := by
  let P := p.restrictTo p.edges (fun _ h => h)
  obtain ⟨w, _⟩ := P.exists_directedWalk
  obtain ⟨w'⟩ := project_walk (fun x : Node G label => base x.val)
    (restrictEdges G (representedEdges G label p)) (fun x y h => by
      rcases rawAdj_cases G label h.1 with he | ⟨he, hx, hy⟩
      · exact Or.inl he
      · exact Or.inr ⟨he, represented_of_path_edge G label p h.2 he hx hy⟩) w
  obtain ⟨q, _⟩ := w'.exists_simplePath
  exact ⟨q.forgetRestriction, q.forgetRestriction_edges_subset⟩

omit [Fintype V] in
/-- Distinct edges on a simple path have distinct tails. -/
theorem path_tail_injective {G : Digraph V} {s t : V} (q : SimplePath G s t) :
    Set.InjOn (fun e : V × V => e.1) q.edges := by
  intro e he f hf h
  obtain ⟨i, rfl⟩ := (q.mem_edges e).mp he
  obtain ⟨j, rfl⟩ := (q.mem_edges f).mp hf
  have hij := q.injective h
  have hval := congrArg Fin.val hij
  have : i = j := Fin.ext hval
  subst j
  rfl

omit [Fintype V] in
/-- Distinct edges on a simple path have distinct heads. -/
theorem path_head_injective {G : Digraph V} {s t : V} (q : SimplePath G s t) :
    Set.InjOn (fun e : V × V => e.2) q.edges := by
  intro e he f hf h
  obtain ⟨i, rfl⟩ := (q.mem_edges e).mp he
  obtain ⟨j, rfl⟩ := (q.mem_edges f).mp hf
  have hij := q.injective h
  have hval := congrArg Fin.val hij
  have : i = j := Fin.ext (by simpa using hval)
  subst j
  rfl

omit [Fintype L] in
/-- Two labels are counted for every projected simple-path edge; injectivity of
original path tails and heads prevents double-counting merged gadget labels. -/
theorem projected_weight_le (G : Digraph V) (label : V × V → L)
    (value : L → ℝ≥0) {s t : V}
    (p : SimplePath (graph G label) (source G label s) (target G label t))
    (q : SimplePath G s t) (hq : q.edges ⊆ representedEdges G label p) :
    2 * q.edgeWeight (value ∘ label) ≤ p.weight (weight G label value) := by
  let R := q.edges.image (right label)
  let S := q.edges.image (left label)
  have hr : Set.InjOn (right label) q.edges := by
    intro e he f hf h
    apply path_tail_injective q he hf
    exact congrArg base h
  have hl : Set.InjOn (left label) q.edges := by
    intro e he f hf h
    apply path_head_injective q he hf
    exact congrArg base h
  have hd : Disjoint R S := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨f, _, hf⟩ := Finset.mem_image.mp hy
    simp [right, left] at hf
  have hsub : R ∪ S ⊆ p.internalVertices.image Subtype.val := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp (hq he)).2.1
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp (hq he)).2.2
  calc
    2 * q.edgeWeight (value ∘ label) =
        (∑ x ∈ R ∪ S, rawWeight G label value x) := by
      rw [Finset.sum_union hd]
      dsimp only [R, S]
      rw [Finset.sum_image hr, Finset.sum_image hl]
      have hR : (∑ e ∈ q.edges, rawWeight G label value (right label e)) =
          q.edgeWeight (value ∘ label) := by
        apply Finset.sum_congr rfl
        intro e he
        exact rawWeight_right G label value (q.edges_subset_graphEdges he)
      have hS : (∑ e ∈ q.edges, rawWeight G label value (left label e)) =
          q.edgeWeight (value ∘ label) := by
        apply Finset.sum_congr rfl
        intro e he
        exact rawWeight_left G label value (q.edges_subset_graphEdges he)
      rw [hR, hS]
      ring
    _ ≤ ∑ x ∈ p.internalVertices.image Subtype.val, rawWeight G label value x :=
      Finset.sum_le_sum_of_subset hsub
    _ = p.weight (weight G label value) := by
      rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
      rfl

/-- A walk enters an original vertex at its start port or an incoming left label. -/
def Entry (u : V) (x : RawNode V L) : Prop :=
  x = start u ∨ ∃ i, x = .inr (u, false, i)

omit [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L] in
theorem entry_to_right (G : Digraph V) (label : V × V → L) {u v : V}
    {x : RawNode V L} (hx : Entry u x) : RawAdj G label x (right label (u, v)) := by
  rcases hx with rfl | ⟨i, rfl⟩ <;> simp [RawAdj, start, right]

omit [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L] in
theorem entry_to_finish (G : Digraph V) (label : V × V → L) {u : V}
    {x : RawNode V L} (hx : Entry u x) : RawAdj G label x (finish u) := by
  rcases hx with rfl | ⟨i, rfl⟩ <;> simp [RawAdj, start, finish]

omit [Fintype L] in
/-- Lift an actual edge-avoiding walk through actual biclique arcs in the
endpoint-retaining vertex-deleted graph. This includes the empty original walk. -/
theorem lift_deleted_walk (G : Digraph V) (label : V × V → L)
    (Y : Finset (Node G label)) (s t : V) {u : V}
    (q : DirectedWalk (edgeDeletedGraph G (pullback G label Y)) u t) :
    ∀ x : {x : Node G label // Retained Y (source G label s) (target G label t) x},
      Entry u x.val.val →
      Nonempty (DirectedWalk
        (endpointDeletedGraph (graph G label) Y (source G label s) (target G label t))
        x (retainedTarget Y (source G label s) (target G label t))) := by
  induction q with
  | refl u =>
    intro x hx
    refine ⟨.cons (u := retainedTarget Y (source G label s) (target G label u))
      ?_ (.refl _)⟩
    exact entry_to_finish G label hx
  | @cons u v t ha q ih =>
    intro x hx
    have he : (u, v) ∈ graphEdges G := (mem_graphEdges G _).mpr ha.1
    let r : Node G label := ⟨right label (u, v), active_right G label he⟩
    let l : Node G label := ⟨left label (u, v), active_left G label he⟩
    have hr : r ∉ Y := by
      intro h
      apply ha.2
      apply (mem_pullback G label Y _).mpr
      exact ⟨he, Or.inl (Finset.mem_image.mpr ⟨r, h, rfl⟩)⟩
    have hl : l ∉ Y := by
      intro h
      apply ha.2
      apply (mem_pullback G label Y _).mpr
      exact ⟨he, Or.inr (Finset.mem_image.mpr ⟨l, h, rfl⟩)⟩
    let r' : {x : Node G label // Retained Y (source G label s) (target G label t) x} :=
      ⟨r, Or.inl hr⟩
    let l' : {x : Node G label // Retained Y (source G label s) (target G label t) x} :=
      ⟨l, Or.inl hl⟩
    obtain ⟨tail⟩ := ih l' (Or.inr ⟨label (u, v), rfl⟩)
    have hxl : (endpointDeletedGraph (graph G label) Y
        (source G label s) (target G label t)).Adj x r' := entry_to_right G label hx
    have hrl : (endpointDeletedGraph (graph G label) Y
        (source G label s) (target G label t)).Adj r' l' := by
      change G.Adj u v ∧ label (u, v) = label (u, v) ∧ label (u, v) = label (u, v)
      exact ⟨ha.1, rfl, rfl⟩
    exact ⟨.cons hxl (.cons hrl tail)⟩

omit [Fintype L] in
/-- Endpoint selections in the gadget cannot falsely cut the original demand:
all original avoiding walks lift with the two demand ports retained. -/
theorem pullback_cutsPair (G : Digraph V) (label : V × V → L)
    (Y : Finset (Node G label)) (s t : V)
    (h : CutsPair (graph G label) Y (source G label s) (target G label t)) :
    EdgeCutsPair G (pullback G label Y) s t := by
  rw [edgeCutsPair_iff_no_deleted_walk]
  rintro ⟨q⟩
  obtain ⟨r⟩ := lift_deleted_walk G label Y s t q
    (retainedSource Y (source G label s) (target G label t)) (Or.inl rfl)
  exact (cutsPair_iff_endpointDeletedGraph (graph G label) Y
    (source G label s) (target G label t)).mp h
      (nonempty_simplePath_iff_directedWalk.mpr ⟨r⟩)

omit [Fintype L] in
/-- The only metric property needed from dyadic rounding: light-edge loss is
at most `1/(2n)` per original edge, while a capped heavy edge retains weight1. -/
theorem threshold_transfer (G : Digraph V) (label : V × V → L)
    (value : L → ℝ≥0) (w : V × V → ℝ≥0)
    (hsmall : ∀ e, w e < 1 →
      w e ≤ value (label e) + 1 / (2 * (Fintype.card V : ℝ≥0)))
    (hlarge : ∀ e, 1 ≤ w e → 1 ≤ value (label e))
    {s t : V} (hst : 1 ≤ edgeDistance G w s t) :
    1 ≤ vertexDistance (graph G label) (weight G label value)
      (source G label s) (target G label t) := by
  rw [← ENNReal.coe_one, coe_le_vertexDistance_iff]
  intro p
  obtain ⟨q, hq⟩ := exists_projected_path G label p
  have hp := projected_weight_le G label value p q hq
  have hw : 1 ≤ q.edgeWeight w :=
    (coe_le_edgeDistance_iff G w s t 1).mp hst q
  by_cases heavy : ∃ e ∈ q.edges, 1 ≤ w e
  · obtain ⟨e, he, hwe⟩ := heavy
    have hr : 1 ≤ q.edgeWeight (value ∘ label) :=
      (hlarge e hwe).trans (Finset.single_le_sum (f := value ∘ label) (fun _ _ => bot_le) he)
    nlinarith
  · have hn : 0 < Fintype.card V := lt_of_le_of_lt (Nat.zero_le _) q.edgeLength_lt_card
    have hn0 : (Fintype.card V : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    have hcard : (q.edges.card : ℝ≥0) ≤ (Fintype.card V : ℝ≥0) := by
      have hnat : q.edges.card ≤ Fintype.card V := by
        rw [q.card_edges]
        exact Nat.le_of_lt q.edgeLength_lt_card
      exact_mod_cast hnat
    have hmass : (q.edges.card : ℝ≥0) *
        (1 / (2 * (Fintype.card V : ℝ≥0))) ≤ 1 / 2 := by
      calc
        _ ≤ (Fintype.card V : ℝ≥0) * (1 / (2 * (Fintype.card V : ℝ≥0))) :=
          mul_le_mul_of_nonneg_right hcard bot_le
        _ = _ := by field_simp
    have hsum : q.edgeWeight w ≤ q.edgeWeight (value ∘ label) +
        (q.edges.card : ℝ≥0) * (1 / (2 * (Fintype.card V : ℝ≥0))) := by
      have h : ∀ e ∈ q.edges, w e ≤
          value (label e) + 1 / (2 * (Fintype.card V : ℝ≥0)) := by
        intro e he
        exact hsmall e (lt_of_not_ge fun h => heavy ⟨e, he, h⟩)
      simpa [SimplePath.edgeWeight, Function.comp_def, Finset.sum_add_distrib,
        nsmul_eq_mul] using Finset.sum_le_sum h
    nlinarith

/-- Concrete dyadic assignment for the actual original finite vertex count. -/
def dyadicLabel (w : V × V → ℝ≥0) : V × V → DyadicEdgeWeights.Label (Fintype.card V) :=
  fun e => DyadicEdgeWeights.round (Fintype.card V) (w e)

def dyadicValue : DyadicEdgeWeights.Label (Fintype.card V) → ℝ≥0 :=
  DyadicEdgeWeights.value (Fintype.card V)

omit [DecidableEq V] in
/-- Exact logarithmic finite-size bound; no power-of-two assumption on n. -/
theorem dyadic_card_le (G : Digraph V) (w : V × V → ℝ≥0) :
    Fintype.card (Node G (dyadicLabel w)) ≤
      2 * Fintype.card V * (Nat.log2 (Fintype.card V) + 4) := by
  simpa only [DyadicEdgeWeights.card_label_log2, Nat.add_assoc] using
    card_node_le G (dyadicLabel w)

theorem dyadic_totalWeight_le (G : Digraph V) (w : V × V → ℝ≥0) :
    totalWeight (weight G (dyadicLabel w) (dyadicValue (V := V))) ≤
      4 * totalEdgeWeight G w := by
  have h : totalEdgeWeight G ((dyadicValue (V := V)) ∘ dyadicLabel w) ≤
      2 * totalEdgeWeight G w := by
    unfold totalEdgeWeight
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun e _ => DyadicEdgeWeights.value_round_le_twice _ (w e)
  exact (totalWeight_le G (dyadicLabel w) (dyadicValue (V := V))).trans
    (by nlinarith)

theorem dyadic_weightedCost_le (G : Digraph V) (w c : V × V → ℝ≥0) :
    weightedCost (cost G (dyadicLabel w) c)
      (weight G (dyadicLabel w) (dyadicValue (V := V))) ≤
      4 * weightedEdgeCost G c w := by
  rw [weightedCost_eq]
  have h : weightedEdgeCost G c ((dyadicValue (V := V)) ∘ dyadicLabel w) ≤
      2 * weightedEdgeCost G c w := by
    unfold weightedEdgeCost
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    calc
      c e * _ ≤ c e * (2 * w e) :=
        mul_le_mul_of_nonneg_left (DyadicEdgeWeights.value_round_le_twice _ (w e)) bot_le
      _ = _ := by ring
  nlinarith

theorem dyadic_threshold_transfer (G : Digraph V) (w : V × V → ℝ≥0)
    {s t : V} (h : 1 ≤ edgeDistance G w s t) :
    1 ≤ vertexDistance (graph G (dyadicLabel w))
      (weight G (dyadicLabel w) (dyadicValue (V := V)))
      (source G (dyadicLabel w) s) (target G (dyadicLabel w) t) := by
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  apply threshold_transfer G (dyadicLabel w) (dyadicValue (V := V)) w
    (fun e he => DyadicEdgeWeights.le_value_round_add hn he)
    (fun e he => le_of_eq (DyadicEdgeWeights.value_round_of_one_le hn he).symm) h

/-- An oracle on actual instances with upper bounds on count and total weight.
Its hypothesis makes no unproved monotonicity assertion about exact-parameter
definitions of the flow-cut gap. -/
def BoundedVertexRoundingOracle (N : ℕ) (B α : ℝ≥0) : Prop :=
  ∀ (U : Type u) [Fintype U] [DecidableEq U] (H : Digraph U) (z c : U → ℝ≥0),
    Fintype.card U ≤ N → totalWeight z ≤ B →
      ∃ Y : Finset U, IsIntegralCut H Y (thresholdDemands H z) ∧
        cutCost c Y ≤ α * weightedCost c z

/-- Finite Theorem30, with explicit constants and an actual transformed
instance. The factor is four, with at most `2n(log₂n+4)` retained vertices and
weight at most `4W`. All cut endpoints are zero-weight, zero-cost ports. -/
theorem round_of_bounded_vertex_oracle (G : Digraph V) (w c : V × V → ℝ≥0)
    (D : Set (V × V)) (hD : IsFractionalEdgeCut G w D) (α : ℝ≥0)
    (oracle : BoundedVertexRoundingOracle.{u}
      (2 * Fintype.card V * (Nat.log2 (Fintype.card V) + 4))
      (4 * totalEdgeWeight G w) α) :
    ∃ X : Finset (V × V), X ⊆ graphEdges G ∧ IsIntegralEdgeCut G X D ∧
      edgeCutCost G c X ≤ (4 * α) * weightedEdgeCost G c w := by
  obtain ⟨Y, hY, hc⟩ := oracle (Node G (dyadicLabel w)) (graph G (dyadicLabel w))
    (weight G (dyadicLabel w) (dyadicValue (V := V)))
    (cost G (dyadicLabel w) c) (dyadic_card_le G w) (dyadic_totalWeight_le G w)
  refine ⟨pullback G (dyadicLabel w) Y, ?_, ?_, ?_⟩
  · intro e he
    exact ((mem_pullback G (dyadicLabel w) Y e).mp he).1
  · intro s t hst
    apply pullback_cutsPair G (dyadicLabel w) Y s t
    exact hY _ _ (dyadic_threshold_transfer G w (hD s t hst))
  · calc
      edgeCutCost G c (pullback G (dyadicLabel w) Y) ≤
          cutCost (cost G (dyadicLabel w) c) Y := pullback_cost_le G (dyadicLabel w) c Y
      _ ≤ α * weightedCost (cost G (dyadicLabel w) c)
          (weight G (dyadicLabel w) (dyadicValue (V := V))) := hc
      _ ≤ α * (4 * weightedEdgeCost G c w) :=
        mul_le_mul_of_nonneg_left (dyadic_weightedCost_le G w c) bot_le
      _ = _ := by ring

/-- The implicit threshold demand family used in the statement of Theorem30. -/
theorem threshold_round_of_bounded_vertex_oracle (G : Digraph V)
    (w c : V × V → ℝ≥0) (α : ℝ≥0)
    (oracle : BoundedVertexRoundingOracle.{u}
      (2 * Fintype.card V * (Nat.log2 (Fintype.card V) + 4))
      (4 * totalEdgeWeight G w) α) :
    ∃ X : Finset (V × V), X ⊆ graphEdges G ∧
      IsIntegralEdgeCut G X (edgeThresholdDemands G w) ∧
      edgeCutCost G c X ≤ (4 * α) * weightedEdgeCost G c w :=
  round_of_bounded_vertex_oracle G w c (edgeThresholdDemands G w)
    (isFractionalEdgeCut_thresholdDemands G w) α oracle

omit [DecidableEq V] [DecidableEq L] in
/-- Empty original graphs produce an empty retained gadget. -/
theorem card_node_eq_zero_of_empty (G : Digraph V) (label : V × V → L)
    (h : Fintype.card V = 0) : Fintype.card (Node G label) = 0 := by
  have hh := card_node_le G label
  simp only [h, mul_zero, zero_mul, nonpos_iff_eq_zero] at hh
  exact hh

omit [Fintype V] in
/-- Self-demands never belong to the original threshold family, even if the
original graph has positive-weight self-loops. -/
@[simp] theorem self_not_threshold (G : Digraph V) (w : V × V → ℝ≥0) (s : V) :
    (s, s) ∉ edgeThresholdDemands G w := by
  simp [edgeThresholdDemands]

omit [Fintype L] in
/-- Selected nonedges can never occur in the pulled-back cut. -/
theorem nonedge_not_pullback (G : Digraph V) (label : V × V → L)
    (Y : Finset (Node G label)) {e : V × V} (h : ¬G.Adj e.1 e.2) :
    e ∉ pullback G label Y := by
  simp [mem_pullback, h]

omit [DecidableEq V] [Fintype L] [DecidableEq L] in
@[simp] theorem weight_source (G : Digraph V) (label : V × V → L)
    (value : L → ℝ≥0) (v : V) : weight G label value (source G label v) = 0 :=
  rawWeight_start G label value v

omit [DecidableEq V] [Fintype L] [DecidableEq L] in
@[simp] theorem weight_target (G : Digraph V) (label : V × V → L)
    (value : L → ℝ≥0) (v : V) : weight G label value (target G label v) = 0 :=
  rawWeight_finish G label value v

omit [Fintype L] in
@[simp] theorem cost_source (G : Digraph V) (label : V × V → L)
    (c : V × V → ℝ≥0) (v : V) : cost G label c (source G label v) = 0 :=
  rawCost_start G label c v

omit [Fintype L] in
@[simp] theorem cost_target (G : Digraph V) (label : V × V → L)
    (c : V × V → ℝ≥0) (v : V) : cost G label c (target G label v) = 0 :=
  rawCost_finish G label c v

omit [DecidableEq V] [Fintype L] [DecidableEq L] in
/-- Every actual original edge, including a loop, has its specified gadget arc. -/
theorem mapped_arc (G : Digraph V) (label : V × V → L) {e : V × V}
    (he : e ∈ graphEdges G) :
    (graph G label).Adj ⟨right label e, active_right G label he⟩
      ⟨left label e, active_left G label he⟩ := by
  exact ⟨(mem_graphEdges G e).mp he, rfl, rfl⟩

omit [DecidableEq V] [Fintype L] [DecidableEq L] in
/-- The additional zero-cost port arc represents a length-zero original walk. -/
theorem empty_walk_arc (G : Digraph V) (label : V × V → L) (v : V) :
    (graph G label).Adj (source G label v) (target G label v) := rfl

end
end EdgeToVertex
end DirectedFlowCutGap
