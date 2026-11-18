import DirectedFlowCutGap.EdgeModel

/-!
# Edge lengths as interior vertex lengths

Each ordered pair has a line-graph node. Only graph edges can be entered.
Distinct source and sink ports keep every traversed edge in the interior
of the lifted path. A direct port-to-port arc represents a self demand.
-/

namespace DirectedFlowCutGap.EdgeLineReduction

open scoped NNReal ENNReal

variable {V : Type*}

abbrev Node (V : Type*) := (V × Bool) ⊕ (V × V)

def start (s : V) : Node V := .inl (s, true)
def finish (t : V) : Node V := .inl (t, false)
def arc (e : V × V) : Node V := .inr e

@[simp] theorem arc_injective : Function.Injective (arc : V × V → Node V) := Sum.inr_injective

def base : Node V → V
  | .inl (v, _) => v
  | .inr (_, v) => v

def departs : Node V → Bool
  | .inl (_, b) => b
  | .inr _ => true

def adjacency (G : Digraph V) (x : Node V) : Node V → Prop
  | .inl (v, false) => departs x = true ∧ base x = v
  | .inl (_, true) => False
  | .inr e => departs x = true ∧ base x = e.1 ∧ G.Adj e.1 e.2

def graph (G : Digraph V) : Digraph (Node V) where
  Adj := adjacency G

theorem departs_of_adj {G : Digraph V} {x y : Node V}
    (h : (graph G).Adj x y) : departs x = true := by
  rcases y with ⟨_, b⟩ | _
  · cases b
    · exact h.1
    · exact False.elim h
  · exact h.1

variable [DecidableEq V]

/-- Incoming arc nodes correspond to precisely the original edges traversed. -/
theorem project_walk {G : Digraph V} {x y : Node V} (q : DirectedWalk (graph G) x y) :
    ∃ p : DirectedWalk G (base x) (base y), ∀ e ∈ p.edges, arc e ∈ q.vertices := by
  induction q with
  | refl x =>
    exact ⟨.refl _, by simp [DirectedWalk.edges]⟩
  | @cons x y z h q ih =>
    obtain ⟨p, hp⟩ := ih
    rcases y with ⟨v, b⟩ | ⟨u, v⟩
    · cases b
      · have he : base x = v := h.2
        subst v
        exact ⟨p, fun e he => Finset.mem_insert_of_mem (hp e he)⟩
      · exact False.elim h
    · have hu : base x = u := h.2.1
      subst u
      have he : G.Adj (base x) v := h.2.2
      refine ⟨.cons he p, ?_⟩
      intro e hm
      rcases Finset.mem_insert.mp hm with hEq | hm
      · subst e
        exact Finset.mem_insert_of_mem q.source_mem_vertices
      · exact Finset.mem_insert_of_mem (hp e hm)

theorem lift_walk {G : Digraph V} {s t : V} (p : DirectedWalk G s t) (x : Node V)
    (hx : departs x = true) (hs : base x = s) :
    ∃ q : DirectedWalk (graph G) x (finish t),
      ∀ e, arc e ∈ q.vertices → arc e = x ∨ e ∈ p.edges := by
  induction p generalizing x with
  | refl s =>
    have h : (graph G).Adj x (finish s) := ⟨hx, hs⟩
    refine ⟨.cons h (.refl _), ?_⟩
    intro e he
    apply Or.inl
    simpa [DirectedWalk.vertices, arc, finish] using he
  | @cons s u t h p ih =>
    obtain ⟨q, hq⟩ := ih (arc (s, u)) rfl rfl
    have hstep : (graph G).Adj x (arc (s, u)) := ⟨hx, hs, h⟩
    refine ⟨.cons hstep q, ?_⟩
    intro e he
    rcases Finset.mem_insert.mp he with he | he
    · exact Or.inl he
    · apply Or.inr
      rcases hq e he with heq | hm
      · exact Finset.mem_insert.mpr (Or.inl (arc_injective heq))
      · exact Finset.mem_insert_of_mem hm

private theorem changeGraph_edges {G H : Digraph V} (h : ∀ s t, G.Adj s t → H.Adj s t)
    {s t : V} (p : DirectedWalk G s t) : (p.changeGraph h).edges = p.edges := by
  induction p with
  | refl => rfl
  | cons _ _ ih => simp [DirectedWalk.changeGraph, DirectedWalk.edges, ih]

private theorem exists_walk_edges {G : Digraph V} {s t : V} (p : SimplePath G s t) :
    ∃ q : DirectedWalk G s t, q.edges ⊆ p.edges := by
  obtain ⟨q, _⟩ := (p.restrictTo p.edges Finset.Subset.rfl).exists_directedWalk
  let forget : ∀ a b, (restrictEdges G p.edges).Adj a b → G.Adj a b := fun _ _ h => h.1
  refine ⟨q.changeGraph forget, ?_⟩
  rw [changeGraph_edges]
  exact fun _ he => (q.edge_adj he).2

noncomputable section

variable [Fintype V]

def arcs (S : Finset (Node V)) : Finset (V × V) :=
  Finset.univ.filter fun e => arc e ∈ S

@[simp] theorem mem_arcs (S : Finset (Node V)) (e : V × V) :
    e ∈ arcs S ↔ arc e ∈ S := by simp [arcs]

def vertexWeight (w : V × V → ℝ≥0) : Node V → ℝ≥0
  | .inl _ => 0
  | .inr e => w e

theorem weight_sum (S : Finset (Node V)) (w : V × V → ℝ≥0) :
    (∑ x ∈ S, vertexWeight w x) = ∑ e ∈ arcs S, w e := by
  calc
    _ = ∑ x ∈ (arcs S).image arc, vertexWeight w x := by
      symm
      apply Finset.sum_subset
      · intro x hx
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
        exact (mem_arcs S e).mp he
      · intro x hx h
        cases x with
        | inl => rfl
        | inr e => exact False.elim (h (Finset.mem_image.mpr ⟨e, (mem_arcs S e).mpr hx, rfl⟩))
    _ = _ := by
      rw [Finset.sum_image (fun _ _ _ _ h => arc_injective h)]
      rfl

theorem project_path {G : Digraph V} {s t : V} (q : SimplePath (graph G) (start s) (finish t)) :
    ∃ p : SimplePath G s t, p.edges ⊆ arcs q.internalVertices := by
  obtain ⟨r, hr⟩ := q.exists_directedWalk
  obtain ⟨p, hp⟩ := project_walk r
  obtain ⟨p', hp'⟩ := p.exists_simplePath_edges_subset
  refine ⟨p', ?_⟩
  intro e he
  exact (mem_arcs _ _).mpr ((q.mem_internalVertices _).mpr
    ⟨(q.mem_vertices _).mp (hr (hp e (hp' he))), by simp [arc, start], by simp [arc, finish]⟩)

theorem lift_path {G : Digraph V} {s t : V} (p : SimplePath G s t) :
    ∃ q : SimplePath (graph G) (start s) (finish t), arcs q.internalVertices ⊆ p.edges := by
  obtain ⟨r, hr⟩ := exists_walk_edges p
  obtain ⟨q, hq⟩ := lift_walk r (start s) rfl rfl
  obtain ⟨q', hq'⟩ := q.exists_simplePath
  refine ⟨q', ?_⟩
  intro e he
  have hv := ((q'.mem_internalVertices (arc e)).mp ((mem_arcs _ _).mp he)).1
  have h := hq' ((q'.mem_vertices (arc e)).mpr hv)
  rcases hq e h with h | h
  · simp [start, arc] at h
  · exact hr h

theorem distance_eq (G : Digraph V) (w : V × V → ℝ≥0) (s t : V) :
    vertexDistance (graph G) (vertexWeight w) (start s) (finish t) = edgeDistance G w s t := by
  apply le_antisymm
  · apply (le_edgeDistance_iff G w s t _).mpr
    intro p
    obtain ⟨q, hq⟩ := lift_path p
    apply (vertexDistance_le_weight (vertexWeight w) q).trans
    rw [SimplePath.weight, weight_sum]
    exact ENNReal.coe_le_coe.mpr (Finset.sum_le_sum_of_subset hq)
  · apply (le_vertexDistance_iff (graph G) (vertexWeight w) (start s) (finish t) _).mpr
    intro q
    obtain ⟨p, hp⟩ := project_path q
    apply (edgeDistance_le_weight w p).trans
    rw [SimplePath.weight, weight_sum]
    exact ENNReal.coe_le_coe.mpr (Finset.sum_le_sum_of_subset hp)

omit [Fintype V] in
theorem internal_is_arc {G : Digraph V} {s t : Node V}
    (q : SimplePath (graph G) s t) {x : Node V} (hx : x ∈ q.internalVertices) :
    ∃ e, x = arc e := by
  rcases x with ⟨v, b⟩ | e
  · obtain ⟨⟨i, hi⟩, hstart, hfinish⟩ :=
      (q.mem_internalVertices (.inl (v, b))).mp hx
    exfalso
    cases b
    · have hlast : i ≠ Fin.last q.edgeLength := fun h =>
        hfinish (hi.symm.trans ((congrArg q.vertex h).trans q.target_eq))
      have hj : i.val < q.edgeLength := by
        have hne : i.val ≠ q.edgeLength := fun h => hlast (Fin.ext h)
        omega
      let j : Fin q.edgeLength := ⟨i.val, hj⟩
      have heq : j.castSucc = i := Fin.ext rfl
      have h := q.adjacent j
      rw [heq, hi] at h
      have htrue := departs_of_adj h
      simp [departs] at htrue
    · have hzero : i ≠ 0 := fun h => hstart (hi.symm.trans ((congrArg q.vertex h).trans q.source_eq))
      have hi0 : i.val ≠ 0 := fun h => hzero (Fin.ext h)
      let j : Fin q.edgeLength := ⟨i.val - 1, by omega⟩
      have heq : j.succ = i := Fin.ext (by dsimp [j]; omega)
      have h := q.adjacent j
      rw [heq, hi] at h
      exact h
  · exact ⟨e, rfl⟩

theorem distance_eq_arcWeight (G : Digraph V) (w : Node V → ℝ≥0) (s t : V) :
    vertexDistance (graph G) w (start s) (finish t) = edgeDistance G (w ∘ arc) s t := by
  calc
    _ = vertexDistance (graph G) (vertexWeight (w ∘ arc)) (start s) (finish t) := by
      apply iInf_congr
      intro q
      apply congrArg (fun a : ℝ≥0 => (a : ℝ≥0∞))
      unfold SimplePath.weight
      apply Finset.sum_congr rfl
      intro x hx
      obtain ⟨e, rfl⟩ := internal_is_arc q hx
      rfl
    _ = _ := distance_eq G (w ∘ arc) s t

theorem pullback_cut (G : Digraph V) (S : Finset (Node V)) {s t : V}
    (h : CutsPair (graph G) S (start s) (finish t)) :
    EdgeCutsPair G (arcs S ∩ graphEdges G) s t := by
  intro p
  obtain ⟨q, hq⟩ := lift_path p
  obtain ⟨x, hx, hS⟩ := h q
  obtain ⟨e, rfl⟩ := internal_is_arc q hx
  have he := hq ((mem_arcs _ e).mpr hx)
  exact ⟨e, he, Finset.mem_inter.mpr ⟨(mem_arcs _ e).mpr hS, (mem_graphEdges _ _).mpr (p.edge_adj he)⟩⟩

theorem lift_cut (G : Digraph V) (X : Finset (V × V)) {s t : V} (h : EdgeCutsPair G X s t) :
    CutsPair (graph G) (X.image arc) (start s) (finish t) := by
  intro q
  obtain ⟨p, hp⟩ := project_path q
  obtain ⟨e, he, hX⟩ := h p
  exact ⟨arc e, (mem_arcs _ _).mp (hp he), Finset.mem_image_of_mem _ hX⟩

end
end DirectedFlowCutGap.EdgeLineReduction
