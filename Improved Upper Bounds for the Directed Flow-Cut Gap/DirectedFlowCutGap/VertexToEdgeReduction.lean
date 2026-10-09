import DirectedFlowCutGap.EdgeModel
import DirectedFlowCutGap.VertexRounding

/-!
# The finite vertex-to-edge reduction (Theorem 31)

Each vertex has distinct input and output copies. Split arcs carry its weight
and cost; original arcs become zero-weight connectors. A finite connector cost
strictly above the rounding budget excludes every connector from a returned
cut. Demand endpoints are output(source) and input(target), so neither endpoint
weight is charged. The metric identity is restricted to distinct original
endpoints: original self-demands have zero vertex distance, whereas the split
graph may have a positive or infinite output-to-input cycle distance.

All weights and costs are arbitrary nonnegative finite reals, including zero.
Original self-loops are retained as connectors, distinct from split arcs.
No runtime or main asymptotic flow-cut bound is asserted.
-/

namespace DirectedFlowCutGap.VertexToEdge

noncomputable section
open scoped BigOperators NNReal ENNReal
attribute [local instance] Classical.propDecidable

universe u
variable {V : Type u}

abbrev Node (V : Type*) := V ⊕ V

def input (v : V) : Node V := Sum.inl v
def output (v : V) : Node V := Sum.inr v

def origin : Node V → V := Sum.elim id id

def splitArc (v : V) : Node V × Node V := (input v, output v)
def connector (e : V × V) : Node V × Node V := (output e.1, input e.2)

def graph (G : Digraph V) : Digraph (Node V) where
  Adj a b := match a, b with
    | .inl u, .inr v => u = v
    | .inr u, .inl v => G.Adj u v
    | _, _ => False

def weight (w : V → ℝ≥0) : Node V × Node V → ℝ≥0
  | (.inl u, .inr _) => w u
  | _ => 0

def cost (c : V → ℝ≥0) (M : ℝ≥0) : Node V × Node V → ℝ≥0
  | (.inl u, .inr _) => c u
  | (.inr _, .inl _) => M
  | _ => 0

@[simp] theorem splitArc_injective : Function.Injective (splitArc : V → _) := by
  intro u v h
  exact Sum.inl.inj (congrArg Prod.fst h)

@[simp] theorem connector_injective : Function.Injective (connector : V × V → _) := by
  intro u v h
  exact Prod.ext (Sum.inr.inj (congrArg Prod.fst h))
    (Sum.inl.inj (congrArg Prod.snd h))

@[simp] theorem splitArc_ne_connector (v : V) (e : V × V) :
    splitArc v ≠ connector e := by simp [splitArc, connector, input, output]

@[simp] theorem split_adj (G : Digraph V) (v : V) :
    (graph G).Adj (input v) (output v) := rfl

@[simp] theorem connector_adj (G : Digraph V) (u v : V) :
    (graph G).Adj (output u) (input v) ↔ G.Adj u v := Iff.rfl

@[simp] theorem weight_split (w : V → ℝ≥0) (v : V) : weight w (splitArc v) = w v := rfl
@[simp] theorem weight_connector (w : V → ℝ≥0) (e : V × V) :
    weight w (connector e) = 0 := rfl
@[simp] theorem cost_split (c : V → ℝ≥0) (M : ℝ≥0) (v : V) :
    cost c M (splitArc v) = c v := rfl
@[simp] theorem cost_connector (c : V → ℝ≥0) (M : ℝ≥0) (e : V × V) :
    cost c M (connector e) = M := rfl

theorem edge_shapes (G : Digraph V) {e : Node V × Node V}
    (h : (graph G).Adj e.1 e.2) :
    (∃ v, e = splitArc v) ∨ (∃ u v, G.Adj u v ∧ e = connector (u, v)) := by
  rcases e with ⟨a, b⟩
  cases a with
  | inl u =>
    cases b with
    | inl v => exact False.elim h
    | inr v =>
      change u = v at h
      subst v
      exact Or.inl ⟨u, rfl⟩
  | inr u =>
    cases b with
    | inl v => exact Or.inr ⟨u, v, h, rfl⟩
    | inr v => exact False.elim h

@[simp] theorem card_nodes [Fintype V] : Fintype.card (Node V) = 2 * Fintype.card V := by
  simp [Node, two_mul]

@[simp] theorem total_weight [Fintype V] (G : Digraph V) (w : V → ℝ≥0) :
    totalEdgeWeight (graph G) (weight w) = totalWeight w := by
  classical
  unfold totalEdgeWeight graphEdges
  rw [Finset.sum_filter]
  simp [Fintype.sum_prod_type, Fintype.sum_sum_type, graph, weight, totalWeight]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

@[simp] theorem weighted_cost [Fintype V] (G : Digraph V) (c w : V → ℝ≥0) (M : ℝ≥0) :
    weightedEdgeCost (graph G) (cost c M) (weight w) = weightedCost c w := by
  classical
  unfold weightedEdgeCost graphEdges
  rw [Finset.sum_filter]
  simp [Fintype.sum_prod_type, Fintype.sum_sum_type, graph, weight, cost, weightedCost]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

variable [DecidableEq V]

/-- Project actual walks. Every projected vertex other than an exposed output
source or input target has traversed its split arc. -/
theorem project_walk {G : Digraph V} {a b : Node V}
    (q : DirectedWalk (graph G) a b) :
    ∃ r : DirectedWalk G (origin a) (origin b),
      ∀ v ∈ r.vertices, a = output v ∨ b = input v ∨ splitArc v ∈ q.edges := by
  induction q with
  | refl a =>
    cases a with
    | inl a =>
      refine ⟨.refl a, ?_⟩
      intro v hv
      have hv' : v = a := by simpa [DirectedWalk.vertices, origin] using hv
      subst v
      exact Or.inr (Or.inl rfl)
    | inr a =>
      refine ⟨.refl a, ?_⟩
      intro v hv
      have hv' : v = a := by simpa [DirectedWalk.vertices, origin] using hv
      subst v
      exact Or.inl rfl
  | @cons a b t h q ih =>
    obtain ⟨r, hr⟩ := ih
    cases a with
    | inl a =>
      cases b with
      | inl b => exact False.elim h
      | inr b =>
        change a = b at h
        subst b
        refine ⟨r, ?_⟩
        intro v hv
        rcases hr v hv with hs | ht | he
        · have hav : a = v := Sum.inr.inj hs
          subst v
          exact Or.inr (Or.inr (Finset.mem_insert_self _ _))
        · exact Or.inr (Or.inl ht)
        · exact Or.inr (Or.inr (Finset.mem_insert_of_mem he))
    | inr a =>
      cases b with
      | inl b =>
        refine ⟨.cons h r, ?_⟩
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Or.inl rfl
        · rcases hr v hv with hs | ht | he
          · simp [output] at hs
          · exact Or.inr (Or.inl ht)
          · exact Or.inr (Or.inr (Finset.mem_insert_of_mem he))
      | inr b => exact False.elim h

/-- Lift a nonempty original vertex sequence, leaving both endpoint split arcs out. -/
def liftSequence {G : Digraph V} : (n : ℕ) → (v : Fin (n + 2) → V) →
    (∀ i : Fin (n + 1), G.Adj (v i.castSucc) (v i.succ)) →
    DirectedWalk (graph G) (output (v 0)) (input (v (Fin.last (n + 1))))
  | 0, v, h => .cons (u := input (v 1)) (h 0) (.refl _)
  | n + 1, v, h => .cons (u := input (v 1)) (h 0)
      (.cons (u := output (v 1)) rfl
        (liftSequence n (fun i => v i.succ) (fun i => h i.succ)))

omit [DecidableEq V] in
theorem liftSequence_weight {G : Digraph V} (n : ℕ) (v : Fin (n + 2) → V)
    (h : ∀ i : Fin (n + 1), G.Adj (v i.castSucc) (v i.succ)) (w : V → ℝ≥0) :
    (liftSequence n v h).edgeWeight (weight w) =
      ∑ i : Fin n, w (v i.succ.castSucc) := by
  induction n with
  | zero => simp [liftSequence, DirectedWalk.edgeWeight, weight, input, output]
  | succ n ih =>
    change 0 + (w (v 1) +
      (liftSequence n (fun i => v i.succ) (fun i => h i.succ)).edgeWeight (weight w)) = _
    rw [zero_add, ih, Fin.sum_univ_succ]
    rfl

theorem liftSequence_split_support {G : Digraph V} (n : ℕ) (v : Fin (n + 2) → V)
    (h : ∀ i : Fin (n + 1), G.Adj (v i.castSucc) (v i.succ)) (x : V) :
    splitArc x ∈ (liftSequence n v h).edges →
      ∃ i : Fin n, v i.succ.castSucc = x := by
  induction n with
  | zero => simp [liftSequence, DirectedWalk.edges, splitArc, input, output]
  | succ n ih =>
    intro hx
    change splitArc x ∈ insert (output (v 0), input (v 1))
      (insert (splitArc (v 1))
        (liftSequence n (fun i => v i.succ) (fun i => h i.succ)).edges) at hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact (splitArc_ne_connector x (v 0, v 1) hx).elim
    rcases Finset.mem_insert.mp hx with hx | hx
    · have hx' : x = v 1 := splitArc_injective hx
      exact ⟨0, hx'.symm⟩
    · obtain ⟨i, hi⟩ := ih (fun i => v i.succ) (fun i => h i.succ) hx
      exact ⟨i.succ, hi⟩

/-- The internal indices of an injective nonempty path are exactly 1 through n. -/
theorem internal_sequence (n : ℕ) (v : Fin (n + 2) → V) (hi : Function.Injective v) :
    (Finset.univ.image v) \ {v 0, v (Fin.last (n + 1))} =
      Finset.univ.image (fun i : Fin n => v i.succ.castSucc) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · rintro ⟨⟨i, rfl⟩, h0, hn⟩
    have hi0 : i.val ≠ 0 := by
      intro h
      exact h0 (congrArg v (Fin.ext h))
    have hin : i.val ≠ n + 1 := by
      intro h
      exact hn (congrArg v (Fin.ext h))
    refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
    congr 1
    apply Fin.ext
    simp
    omega
  · rintro ⟨i, rfl⟩
    refine ⟨⟨i.succ.castSucc, rfl⟩, ?_, ?_⟩
    · intro h
      have hh := congrArg Fin.val (hi h)
      simp at hh
    · intro h
      have hh := congrArg Fin.val (hi h)
      simp at hh
      omega

/-- A genuine original simple path lifts with exactly its internal weight.
Only split arcs of its internal vertices occur in the lifted walk. -/
theorem lift_path {G : Digraph V} {s t : V} (hst : s ≠ t)
    (p : SimplePath G s t) (w : V → ℝ≥0) :
    ∃ q : DirectedWalk (graph G) (output s) (input t),
      q.edgeWeight (weight w) = p.weight w ∧
      ∀ v, splitArc v ∈ q.edges → v ∈ p.internalVertices := by
  cases p with
  | mk m v hs ht hi ha =>
    subst s
    subst t
    cases m with
    | zero => exact (hst rfl).elim
    | succ n =>
      refine ⟨liftSequence n v ha, ?_, ?_⟩
      · rw [liftSequence_weight]
        change _ = ∑ x ∈ (Finset.univ.image v) \ {v 0, v (Fin.last (n + 1))}, w x
        rw [internal_sequence n v hi, Finset.sum_image]
        intro i _ j _ hij
        have hh := congrArg Fin.val (hi hij)
        apply Fin.ext
        simp at hh
        omega
      · intro x hx
        obtain ⟨i, rfl⟩ := liftSequence_split_support n v ha x hx
        change v i.succ.castSucc ∈
          (Finset.univ.image v) \ {v 0, v (Fin.last (n + 1))}
        rw [internal_sequence n v hi]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- Changing adjacency proofs leaves every traversed ordered pair unchanged. -/
theorem walk_changeGraph_edges {U : Type*} [DecidableEq U] {H K : Digraph U}
    (h : ∀ a b, H.Adj a b → K.Adj a b) {s t : U} (q : DirectedWalk H s t) :
    (q.changeGraph h).edges = q.edges := by
  induction q with
  | refl => rfl
  | cons ha q ih => simp [DirectedWalk.changeGraph, DirectedWalk.edges, ih]

/-- A simple path also has a walk using only its actual edges. -/
theorem path_walk_support {U : Type*} [DecidableEq U] {H : Digraph U} {s t : U}
    (p : SimplePath H s t) :
    ∃ q : DirectedWalk H s t, q.edges ⊆ p.edges := by
  obtain ⟨q, _hq⟩ := (p.restrictTo p.edges (fun _ h => h)).exists_directedWalk
  refine ⟨q.changeGraph (G := restrictEdges H p.edges) (H := H) (fun _ _ h => h.1), ?_⟩
  rw [walk_changeGraph_edges]
  intro e he
  exact (q.edge_adj he).2

/-- Project and erase loops while retaining every internal vertex's split arc. -/
theorem project_path {G : Digraph V} {s t : V}
    (p : SimplePath (graph G) (output s) (input t)) :
    ∃ r : SimplePath G s t,
      ∀ v ∈ r.internalVertices, splitArc v ∈ p.edges := by
  obtain ⟨q, hq⟩ := path_walk_support p
  obtain ⟨r, hr⟩ := project_walk q
  obtain ⟨a, ha⟩ := r.exists_simplePath
  refine ⟨a, ?_⟩
  intro v hv
  obtain ⟨hvm, hvs, hvt⟩ := (a.mem_internalVertices v).mp hv
  have hmem : v ∈ r.vertices := ha ((a.mem_vertices v).mpr hvm)
  rcases hr v hmem with hs | ht | he
  · exact (hvs (Sum.inr.inj hs).symm).elim
  · exact (hvt (Sum.inl.inj ht).symm).elim
  · exact hq he

theorem project_path_weight {G : Digraph V} {s t : V}
    (p : SimplePath (graph G) (output s) (input t)) (w : V → ℝ≥0) :
    ∃ r : SimplePath G s t, r.weight w ≤ p.edgeWeight (weight w) := by
  obtain ⟨r, hr⟩ := project_path p
  refine ⟨r, ?_⟩
  calc
    r.weight w = ∑ e ∈ r.internalVertices.image splitArc, weight w e := by
      rw [Finset.sum_image]
      · rfl
      · intro a _ b _ hab
        exact splitArc_injective hab
    _ ≤ p.edgeWeight (weight w) := Finset.sum_le_sum_of_subset (by
      intro e he
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
      exact hr v hv)

/-- Exact metric bridge for distinct original demands only. -/
theorem distance_eq {G : Digraph V} (w : V → ℝ≥0) {s t : V} (hst : s ≠ t) :
    edgeDistance (graph G) (weight w) (output s) (input t) =
      vertexDistance G w s t := by
  apply le_antisymm
  · rw [le_vertexDistance_iff]
    intro p
    obtain ⟨q, hq, _⟩ := lift_path hst p w
    simpa [hq] using edgeDistance_le_walk_weight (weight w) q
  · rw [le_edgeDistance_iff]
    intro p
    obtain ⟨r, hr⟩ := project_path_weight p w
    exact (vertexDistance_le_weight w r).trans (ENNReal.coe_le_coe.mpr hr)

variable [Fintype V]

/-- Select exactly the original vertices whose split arcs were selected. -/
def pullCut (X : Finset (Node V × Node V)) : Finset V :=
  Finset.univ.filter (fun v => splitArc v ∈ X)

@[simp] theorem mem_pullCut (X : Finset (Node V × Node V)) (v : V) :
    v ∈ pullCut X ↔ splitArc v ∈ X := by simp [pullCut]

omit [DecidableEq V] [Fintype V] in
/-- Every selected actual connector costs more than the whole allowed budget. -/
theorem no_connector_of_budget (G : Digraph V) (c : V → ℝ≥0) (B M : ℝ≥0)
    (hM : B < M) (X : Finset (Node V × Node V))
    (hX : edgeCutCost (graph G) (cost c M) X ≤ B) :
    ∀ u v, G.Adj u v → connector (u, v) ∉ X := by
  intro u v huv hx
  have hm : M ≤ edgeCutCost (graph G) (cost c M) X := by
    change cost c M (connector (u, v)) ≤ _
    exact Finset.single_le_sum (fun _ _ => bot_le)
      (Finset.mem_filter.mpr ⟨hx, huv⟩)
  exact (not_le_of_gt hM) (hm.trans hX)

theorem selected_actual_edges (G : Digraph V) (X : Finset (Node V × Node V))
    (hX : ∀ u v, G.Adj u v → connector (u, v) ∉ X) :
    X.filter (fun e => (graph G).Adj e.1 e.2) = (pullCut X).image splitArc := by
  ext e
  constructor
  · intro he
    obtain ⟨hx, ha⟩ := Finset.mem_filter.mp he
    rcases edge_shapes G ha with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩
    · exact Finset.mem_image.mpr ⟨v, (mem_pullCut X v).mpr hx, rfl⟩
    · exact (hX u v huv hx).elim
  · intro he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_filter.mpr ⟨(mem_pullCut X v).mp hv, split_adj G v⟩

/-- Exact cost, even if the edge cut contains irrelevant nonedges. -/
theorem pullCut_cost (G : Digraph V) (c : V → ℝ≥0) (M : ℝ≥0)
    (X : Finset (Node V × Node V))
    (hX : ∀ u v, G.Adj u v → connector (u, v) ∉ X) :
    cutCost c (pullCut X) = edgeCutCost (graph G) (cost c M) X := by
  unfold edgeCutCost
  rw [selected_actual_edges G X hX, Finset.sum_image]
  · rfl
  · intro a _ b _ hab
    exact splitArc_injective hab

/-- An edge cut containing no actual connector hits original paths internally. -/
theorem pullCut_cutsPair (G : Digraph V) (X : Finset (Node V × Node V))
    (hX : ∀ u v, G.Adj u v → connector (u, v) ∉ X) {s t : V} (hst : s ≠ t)
    (hc : EdgeCutsPair (graph G) X (output s) (input t)) : CutsPair G (pullCut X) s t := by
  intro p
  obtain ⟨q, _hq, hsupport⟩ := lift_path hst p (fun _ => 0)
  obtain ⟨r, hr⟩ := q.exists_simplePath_edges_subset
  obtain ⟨e, he, hx⟩ := hc r
  rcases edge_shapes G (r.edge_adj he) with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩
  · exact ⟨v, hsupport v (hr he), (mem_pullCut X v).mpr hx⟩
  · exact (hX u v huv hx).elim

/-- The reverse path-cut bridge does not need connector exclusion. -/
theorem edgeCutsPair_of_pullCut (G : Digraph V) (X : Finset (Node V × Node V))
    {s t : V} (hc : CutsPair G (pullCut X) s t) :
    EdgeCutsPair (graph G) X (output s) (input t) := by
  intro p
  obtain ⟨r, hr⟩ := project_path p
  obtain ⟨v, hv, hx⟩ := hc r
  exact ⟨splitArc v, hr v hv, (mem_pullCut X v).mp hx⟩

/-- The cut bridge is exact once actual connectors are excluded. -/
theorem cutsPair_iff_edgeCutsPair (G : Digraph V)
    (X : Finset (Node V × Node V))
    (hX : ∀ u v, G.Adj u v → connector (u, v) ∉ X) {s t : V} (hst : s ≠ t) :
    CutsPair G (pullCut X) s t ↔ EdgeCutsPair (graph G) X (output s) (input t) :=
  ⟨edgeCutsPair_of_pullCut G X, pullCut_cutsPair G X hX hst⟩

omit [Fintype V] in
/-- Self-demands are never among the original threshold-one demands. -/
theorem threshold_distinct (G : Digraph V) (w : V → ℝ≥0) {s t : V}
    (h : (s, t) ∈ thresholdDemands G w) : s ≠ t := by
  intro he
  subst t
  have hh : 1 ≤ vertexDistance G w s s := h
  simp at hh

/-- A bounded oracle is asked only about actual instance size and total weight.
It returns a cut of every edge threshold demand with the stated finite factor. -/
def BoundedEdgeRoundingOracle (N : ℕ) (W α : ℝ≥0) : Prop :=
  ∀ (U : Type u) [Fintype U] [DecidableEq U] (H : Digraph U) (c w : U × U → ℝ≥0),
    Fintype.card U ≤ N → totalEdgeWeight H w ≤ W →
    ∃ X : Finset (U × U),
      IsIntegralEdgeCut H X (edgeThresholdDemands H w) ∧
      edgeCutCost H c X ≤ α * weightedEdgeCost H c w

/-- The exact finite form of Theorem 31. No monotonicity of an abstract gap
function is used: the supplied oracle is at 2n vertices and exactly W. -/
theorem vertex_to_edge_rounding (G : Digraph V) (c w : V → ℝ≥0) (α : ℝ≥0)
    (oracle : BoundedEdgeRoundingOracle.{u} (2 * Fintype.card V) (totalWeight w) α) :
    ∃ Y : Finset V, IsIntegralCut G Y (thresholdDemands G w) ∧
      cutCost c Y ≤ α * weightedCost c w := by
  let B := α * weightedCost c w
  let M := B + 1
  have hM : B < M := lt_add_of_pos_right B zero_lt_one
  obtain ⟨X, hcut, hcost⟩ := oracle (Node V) (graph G) (cost c M) (weight w)
    (by simp [two_mul]) (by simp)
  have hcost' : edgeCutCost (graph G) (cost c M) X ≤ B := by
    simpa [B] using hcost
  have hconn := no_connector_of_budget G c B M hM X hcost'
  refine ⟨pullCut X, ?_, ?_⟩
  · intro s t hst
    have hdist : 1 ≤ vertexDistance G w s t := hst
    have hne : s ≠ t := threshold_distinct G w hst
    apply pullCut_cutsPair G X hconn hne
    apply hcut
    change 1 ≤ edgeDistance (graph G) (weight w) (output s) (input t)
    rw [distance_eq w hne]
    exact hdist
  · rw [pullCut_cost G c M X hconn]
    exact hcost'

/-- The reduction feeds the established finite vertex-rounding interface. -/
theorem hasVertexRoundingFactor_of_bounded_edge_oracle (G : Digraph V)
    (w : V → ℝ≥0) (α : ℝ≥0)
    (oracle : BoundedEdgeRoundingOracle.{u} (2 * Fintype.card V) (totalWeight w) α) :
    HasVertexRoundingFactor G w (α : ℝ) := by
  refine ⟨NNReal.coe_nonneg _, ?_⟩
  intro c
  obtain ⟨Y, hY, hc⟩ := vertex_to_edge_rounding G c w α oracle
  exact ⟨Y, hY, by exact_mod_cast hc⟩

end
end DirectedFlowCutGap.VertexToEdge
