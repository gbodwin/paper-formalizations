import DirectedFlowCutGap.EdgeModel

/-!
# Endpoint-excluding vertex distances as outgoing edge distances

For each fixed demand source, put weight zero on its outgoing edges and put
the weight of the tail on every other edge. On a simple path, the remaining
edge tails are in bijection with the internal vertices. Thus the actual edge
and endpoint-excluding vertex distances agree, including self pairs and
unreachable pairs. No positivity or finite-vertex assumption is needed for
this analytic bridge. Natural grid numerators are included for subsequent
executable shortest-path algorithms.
-/

namespace DirectedFlowCutGap

open scoped BigOperators NNReal ENNReal

namespace VertexGridDistances

variable {V : Type*} [DecidableEq V]

/-- Charge an edge's tail, except for the fixed demand source. -/
def outgoingWeight (w : V → ℝ≥0) (s : V) (e : V × V) : ℝ≥0 :=
  if e.1 = s then 0 else w e.1

private theorem edge_tail_internal {G : Digraph V} {s t : V}
    (p : SimplePath G s t) {e : V × V} (he : e ∈ p.edges) (hs : e.1 ≠ s) :
    e.1 ∈ p.internalVertices := by
  obtain ⟨i, rfl⟩ := (p.mem_edges e).mp he
  refine (p.mem_internalVertices _).mpr ⟨⟨i.castSucc, rfl⟩, hs, ?_⟩
  intro ht
  have hi := congrArg Fin.val (p.injective (ht.trans p.target_eq.symm))
  have hil := i.isLt
  change i.val = p.edgeLength at hi
  omega

private theorem edge_tail_injective {G : Digraph V} {s t : V}
    (p : SimplePath G s t) {e f : V × V} (he : e ∈ p.edges) (hf : f ∈ p.edges)
    (h : e.1 = f.1) : e = f := by
  obtain ⟨i, rfl⟩ := (p.mem_edges e).mp he
  obtain ⟨j, rfl⟩ := (p.mem_edges f).mp hf
  have hij : i = j :=
    Fin.ext (congrArg (fun k : Fin (p.edgeLength + 1) => k.val) (p.injective h))
  exact congrArg p.edgeAt hij

private theorem internal_is_edge_tail {G : Digraph V} {s t : V}
    (p : SimplePath G s t) {v : V} (hv : v ∈ p.internalVertices) :
    ∃ e ∈ p.edges, e.1 ≠ s ∧ e.1 = v := by
  obtain ⟨⟨i, hi⟩, hs, ht⟩ := (p.mem_internalVertices v).mp hv
  have hilt : i.val < p.edgeLength := by
    by_contra hn
    have hiend : i = Fin.last p.edgeLength := Fin.ext (by simp; omega)
    exact ht (hi.symm.trans ((congrArg p.vertex hiend).trans p.target_eq))
  let j : Fin p.edgeLength := ⟨i.val, hilt⟩
  have hj : j.castSucc = i := Fin.ext rfl
  refine ⟨p.edgeAt j, p.edgeAt_mem_edges j, ?_, ?_⟩
  · simpa only [SimplePath.edgeAt, hj, hi] using hs
  · simpa only [SimplePath.edgeAt, hj] using hi

/-- The outgoing-edge encoding preserves every actual simple path's weight. -/
theorem edgeWeight_eq_vertexWeight {G : Digraph V} {s t : V}
    (p : SimplePath G s t) (w : V → ℝ≥0) :
    p.edgeWeight (outgoingWeight w s) = p.weight w := by
  unfold SimplePath.edgeWeight SimplePath.weight
  calc
    (∑ e ∈ p.edges, outgoingWeight w s e) =
        ∑ e ∈ p.edges.filter (fun e => e.1 ≠ s), w e.1 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hs : e.1 = s <;> simp [outgoingWeight, hs]
    _ = ∑ v ∈ p.internalVertices, w v := by
      apply Finset.sum_bij (fun e _he => e.1)
      · intro e he
        exact edge_tail_internal p (Finset.mem_filter.mp he).1
          (Finset.mem_filter.mp he).2
      · intro e he f hf hef
        exact edge_tail_injective p (Finset.mem_filter.mp he).1
          (Finset.mem_filter.mp hf).1 hef
      · intro v hv
        obtain ⟨e, he, hs, hev⟩ := internal_is_edge_tail p hv
        exact ⟨e, Finset.mem_filter.mpr ⟨he, hs⟩, hev⟩
      · intro e _he
        rfl

/-- Exact extended distance, with both original demand endpoints excluded. -/
theorem edgeDistance_eq_vertexDistance (G : Digraph V) (w : V → ℝ≥0) (s t : V) :
    edgeDistance G (outgoingWeight w s) s t = vertexDistance G w s t := by
  unfold edgeDistance vertexDistance
  apply iInf_congr
  intro p
  rw [edgeWeight_eq_vertexWeight]

/-- Natural edge numerators for the source-excluded outgoing-edge encoding. -/
def outgoingNumerator (a : V → ℕ) (s : V) (e : V × V) : ℕ :=
  if e.1 = s then 0 else a e.1

/-- Scaling the natural encoding agrees with encoding the scaled vertex weights. -/
theorem outgoingNumerator_div (a : V → ℕ) (L : ℕ) (s : V) (e : V × V) :
    (outgoingNumerator a s e : ℝ≥0) / L =
      outgoingWeight (fun v => (a v : ℝ≥0) / L) s e := by
  by_cases hs : e.1 = s <;> simp [outgoingNumerator, outgoingWeight, hs]

/-- The natural-grid specialization. Positive denominators are required by
grid algorithms, but the analytic identity itself holds for every denominator. -/
theorem grid_edgeDistance_eq_vertexDistance (G : Digraph V) (a : V → ℕ)
    (L : ℕ) (s t : V) :
    edgeDistance G (fun e => (outgoingNumerator a s e : ℝ≥0) / L) s t =
      vertexDistance G (fun v => (a v : ℝ≥0) / L) s t := by
  simp_rw [outgoingNumerator_div]
  exact edgeDistance_eq_vertexDistance G _ s t

end VertexGridDistances

end DirectedFlowCutGap
