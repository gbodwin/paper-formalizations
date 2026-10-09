import DirectedFlowCutGap.EdgeModel
import DirectedFlowCutGap.PackingCovering

/-!
# Directed edge sum-multiflow duality

This proves the LP interpretation stated in arXiv:2604.03412v3,
`intro.tex:58`, for the actual edge model of `EdgeModel`.

Packing coordinates are actual directed simple paths of the demanded pairs.
Resources are their actual ordered-pair edges, including endpoint incident
edges. Every edge capacity and every objective refers to actual graph edges;
values supplied on nonedges have no effect. The finite incidence LP uses zero
capacity on nonedges to identify its objective exactly with `weightedEdgeCost`.

An actual feasible fractional edge cut is the sole domain hypothesis for
attained duality. It excludes self demands and zero-edge demanded paths.
Distinct adjacent demands are allowed, unlike endpoint-excluding vertex flow.
Empty demands, unreachable demands, graph loops and zero capacities are allowed.
There is no concurrency requirement: the objective sums all routed amounts.
No approximation factor, asymptotic bound or runtime is asserted here.
-/

namespace DirectedFlowCutGap.EdgeFlow

noncomputable section
open scoped BigOperators NNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One coordinate for every actual simple path of every demanded pair. -/
abbrev PathIndex (G : Digraph V) (D : Set (V × V)) :=
  Σ st : D, SimplePath G st.val.1 st.val.2

instance pathIndexFintype (G : Digraph V) (D : Set (V × V)) :
    Fintype (PathIndex G D) := Fintype.ofFinite _

variable {G : Digraph V} {D : Set (V × V)}

/-- All consecutive edges consume capacity, with no endpoint exclusion. -/
def resources (p : PathIndex G D) : Finset (V × V) := p.2.edges

abbrev Flow (G : Digraph V) (D : Set (V × V)) := PathIndex G D → ℝ≥0

/-- Total amount routed through this ordered-pair edge. -/
def load (f : Flow G D) (e : V × V) : ℝ≥0 := by
  classical
  exact ∑ p with e ∈ resources p, f p

def value (f : Flow G D) : ℝ≥0 := ∑ p, f p

/-- Only actual edges have graph capacity constraints. -/
def IsFeasible (capacity : V × V → ℝ≥0) (f : Flow G D) : Prop :=
  ∀ e, G.Adj e.1 e.2 → load f e ≤ capacity e

/-- The incidence LP includes all ordered pairs and assigns nonedges capacity zero. -/
def capacityOnEdges (G : Digraph V) (capacity : V × V → ℝ≥0) (e : V × V) : ℝ≥0 := by
  classical
  exact if G.Adj e.1 e.2 then capacity e else 0

/-- No path can load a nonedge. -/
theorem load_eq_zero_of_nonedge (f : Flow G D) {e : V × V}
    (he : ¬ G.Adj e.1 e.2) : load f e = 0 := by
  classical
  unfold load
  apply Finset.sum_eq_zero
  intro p hp
  exact (he (p.2.edge_adj (Finset.mem_filter.mp hp).2)).elim

theorem incidence_load_eq (f : Flow G D) (e : V × V) :
    PackingCovering.load resources (fun p => (f p : ℝ)) e = (load f e : ℝ) := by
  classical
  rw [PackingCovering.load_eq_sum_filter]
  simp [load, NNReal.coe_sum]

/-- The covering constraint is exactly the full edge weight of the path. -/
theorem incidence_pathWeight_eq (w : V × V → ℝ≥0) (p : PathIndex G D) :
    PackingCovering.pathWeight resources (fun e => (w e : ℝ)) p =
      (p.2.edgeWeight w : ℝ) := by
  rw [PackingCovering.pathWeight_eq_sum]
  simp [resources, SimplePath.edgeWeight, NNReal.coe_sum]

theorem packingValue_eq (f : Flow G D) :
    PackingCovering.packingValue (fun p => (f p : ℝ)) = (value f : ℝ) := by
  simp [PackingCovering.packingValue, value, NNReal.coe_sum]

omit [DecidableEq V] in
/-- Zeroing nonedge capacities gives exactly the actual-edge fractional objective. -/
theorem coveringValue_eq (capacity w : V × V → ℝ≥0) :
    PackingCovering.coveringValue (fun e => (capacityOnEdges G capacity e : ℝ))
      (fun e => (w e : ℝ)) = (weightedEdgeCost G capacity w : ℝ) := by
  classical
  have hs : (∑ e, capacityOnEdges G capacity e * w e) = weightedEdgeCost G capacity w := by
    unfold weightedEdgeCost graphEdges
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : G.Adj e.1 e.2 <;> simp [capacityOnEdges, he]
  rw [← hs]
  simp [PackingCovering.coveringValue, NNReal.coe_sum, NNReal.coe_mul]

/-- The incidence packing constraints and actual edge capacities agree exactly. -/
theorem isPacking_iff (capacity : V × V → ℝ≥0) (f : Flow G D) :
    PackingCovering.IsPacking resources
      (fun e => (capacityOnEdges G capacity e : ℝ))
      (fun p => (f p : ℝ)) ↔ IsFeasible capacity f := by
  constructor
  · intro hf e he
    apply NNReal.coe_le_coe.mp
    rw [← incidence_load_eq]
    simpa [capacityOnEdges, he] using hf.2 e
  · intro hf
    refine ⟨fun p => (f p).coe_nonneg, fun e => ?_⟩
    rw [incidence_load_eq]
    by_cases he : G.Adj e.1 e.2
    · simpa [capacityOnEdges, he] using NNReal.coe_le_coe.mpr (hf e he)
    · simp [capacityOnEdges, he, load_eq_zero_of_nonedge f he]

/-- Exact identification with the all-demand edge distance constraints. -/
theorem isCovering_iff (w : V × V → ℝ≥0) :
    PackingCovering.IsCovering (resources (G := G) (D := D))
      (fun e => (w e : ℝ)) ↔ IsFractionalEdgeCut G w D := by
  rw [isFractionalEdgeCut_iff]
  constructor
  · intro hw s t hst p
    have h := hw.2 (⟨⟨(s, t), hst⟩, p⟩ : PathIndex G D)
    rw [incidence_pathWeight_eq] at h
    exact NNReal.one_le_coe.mp h
  · intro hw
    refine ⟨fun e => (w e).coe_nonneg, ?_⟩
    intro p
    rw [incidence_pathWeight_eq]
    exact NNReal.one_le_coe.mpr (hw _ _ p.1.property p.2)

omit [Fintype V] in
/-- A feasible fractional cut excludes every path without an edge. -/
theorem resources_nonempty_of_fractionalCut {w : V × V → ℝ≥0}
    (hw : IsFractionalEdgeCut G w D) (p : PathIndex G D) :
    (resources p).Nonempty := by
  have hp := (isFractionalEdgeCut_iff G w D).mp hw _ _ p.1.property p.2
  by_contra hempty
  have he : p.2.edges = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  simp [SimplePath.edgeWeight, he] at hp

omit [Fintype V] in
/-- Unit edge weights provide feasibility exactly when no demanded path is empty. -/
theorem exists_fractionalCut_iff :
    (∃ w : V × V → ℝ≥0, IsFractionalEdgeCut G w D) ↔
      ∀ p : PathIndex G D, (resources p).Nonempty := by
  constructor
  · rintro ⟨w, hw⟩
    exact resources_nonempty_of_fractionalCut hw
  · intro h
    refine ⟨fun _ => 1, (isFractionalEdgeCut_iff G _ D).mpr ?_⟩
    intro s t hst p
    have hp := h (⟨⟨(s, t), hst⟩, p⟩ : PathIndex G D)
    change 1 ≤ ∑ e ∈ p.edges, (1 : ℝ≥0)
    simpa using (Nat.one_le_cast.mpr (Finset.card_pos.mpr hp) : (1 : ℝ≥0) ≤ (p.edges.card : ℝ≥0))

omit [Fintype V] in
theorem no_fractionalCut_of_empty_resources (p : PathIndex G D)
    (hp : resources p = ∅) : ¬ ∃ w : V × V → ℝ≥0, IsFractionalEdgeCut G w D := by
  rw [exists_fractionalCut_iff]
  intro h
  simpa [hp] using h p

omit [Fintype V] in
/-- Graph self-loops do not remove the zero-edge self path. -/
theorem no_fractionalCut_of_self {s : V} (hs : (s, s) ∈ D) :
    ¬ ∃ w : V × V → ℝ≥0, IsFractionalEdgeCut G w D := by
  apply no_fractionalCut_of_empty_resources
    (⟨⟨(s, s), hs⟩, SimplePath.refl G s⟩ : PathIndex G D)
  simp [resources]

omit [Fintype V] in
/-- Unlike vertex flow, edge cut feasibility excludes only diagonal demands. -/
theorem exists_fractionalCut_iff_no_self :
    (∃ w : V × V → ℝ≥0, IsFractionalEdgeCut G w D) ↔ ∀ s, (s, s) ∉ D := by
  constructor
  · intro h s hs
    exact no_fractionalCut_of_self hs h
  · intro h
    rw [exists_fractionalCut_iff]
    intro p
    by_contra hn
    have he : p.2.edges = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hl : p.2.edgeLength = 0 := by
      have hh := congrArg Finset.card he
      simpa using hh
    have hi : (0 : Fin (p.2.edgeLength + 1)) = Fin.last p.2.edgeLength := by
      apply Fin.ext
      simpa using hl.symm
    have hst : p.1.val.1 = p.1.val.2 :=
      p.2.source_eq.symm.trans ((congrArg p.2.vertex hi).trans p.2.target_eq)
    apply h p.1.val.1
    have hp : (p.1.val.1, p.1.val.2) ∈ D := p.1.property
    simpa only [← hst] using hp

/-- Graph weak duality is a consequence of the finite incidence inequality. -/
theorem weak_duality {capacity w : V × V → ℝ≥0} {f : Flow G D}
    (hf : IsFeasible capacity f) (hw : IsFractionalEdgeCut G w D) :
    value f ≤ weightedEdgeCost G capacity w := by
  have h := PackingCovering.weak_duality resources
    ((isPacking_iff capacity f).mpr hf) ((isCovering_iff w).mpr hw)
  rw [packingValue_eq, coveringValue_eq] at h
  exact NNReal.coe_le_coe.mp h

/-- Attained maximum directed edge sum-multiflow equals attained minimum
fractional edge cut. The supplied cut need only be feasible. Zero capacities,
empty demand families and unreachable demanded pairs are included. -/
theorem strong_duality (capacity w₀ : V × V → ℝ≥0)
    (hw₀ : IsFractionalEdgeCut G w₀ D) :
    ∃ (f : Flow G D) (w : V × V → ℝ≥0),
      IsFeasible capacity f ∧ IsFractionalEdgeCut G w D ∧
      value f = weightedEdgeCost G capacity w ∧
      (∀ g : Flow G D, IsFeasible capacity g → value g ≤ value f) ∧
      (∀ z : V × V → ℝ≥0, IsFractionalEdgeCut G z D →
        weightedEdgeCost G capacity w ≤ weightedEdgeCost G capacity z) ∧
      (∀ e, w e ≤ 1) := by
  classical
  obtain ⟨fr, wr, hfr, hwr, heq, hmax, hmin, hwr1⟩ :=
    PackingCovering.strong_duality (resources (G := G) (D := D))
      (fun e => (capacityOnEdges G capacity e).coe_nonneg)
      (resources_nonempty_of_fractionalCut hw₀)
  let f : Flow G D := fun p => ⟨fr p, hfr.1 p⟩
  let w : V × V → ℝ≥0 := fun e => ⟨wr e, hwr.1 e⟩
  have hf : IsFeasible capacity f := (isPacking_iff capacity f).mp hfr
  have hw : IsFractionalEdgeCut G w D := (isCovering_iff w).mp hwr
  refine ⟨f, w, hf, hw, ?_, ?_, ?_, ?_⟩
  · apply NNReal.coe_injective
    rw [← packingValue_eq, ← coveringValue_eq]
    exact heq
  · intro g hg
    apply NNReal.coe_le_coe.mp
    rw [← packingValue_eq, ← packingValue_eq]
    exact hmax _ ((isPacking_iff capacity g).mpr hg)
  · intro z hz
    apply NNReal.coe_le_coe.mp
    rw [← coveringValue_eq, ← coveringValue_eq]
    exact hmin _ ((isCovering_iff z).mpr hz)
  · intro e
    exact NNReal.coe_le_one.mp (hwr1 e)

omit [Fintype V] [DecidableEq V] in
/-- Unreachable demands produce no packing coordinates. -/
theorem isEmpty_pathIndex_iff :
    IsEmpty (PathIndex G D) ↔
      ∀ s t, (s, t) ∈ D → ¬ Nonempty (SimplePath G s t) := by
  constructor
  · intro h s t hst hp
    exact h.false ⟨⟨(s, t), hst⟩, hp.some⟩
  · intro h
    exact ⟨fun p => h _ _ p.1.property ⟨p.2⟩⟩

theorem value_eq_zero_of_unreachable
    (h : ∀ s t, (s, t) ∈ D → ¬ Nonempty (SimplePath G s t)) (f : Flow G D) :
    value f = 0 := by
  let : IsEmpty (PathIndex G D) := isEmpty_pathIndex_iff.mpr h
  simp [value]

omit [Fintype V] in
theorem zero_isFractionalCut_of_unreachable
    (h : ∀ s t, (s, t) ∈ D → ¬ Nonempty (SimplePath G s t)) :
    IsFractionalEdgeCut G (fun _ => 0) D := by
  rw [isFractionalEdgeCut_iff]
  intro s t hst p
  exact (h s t hst ⟨p⟩).elim

omit [Fintype V] in
theorem zero_isFractionalCut_empty (G : Digraph V) :
    IsFractionalEdgeCut G (fun _ => 0) ∅ := by
  intro s t hst
  exact hst.elim

theorem value_eq_zero_empty (f : Flow G ∅) : value f = 0 :=
  value_eq_zero_of_unreachable (fun _ _ h => h.elim) f

/-- On the feasible-cut domain, zero actual edge capacities force zero flow. -/
theorem value_eq_zero_of_zero_capacity {w₀ : V × V → ℝ≥0}
    (hw₀ : IsFractionalEdgeCut G w₀ D) {f : Flow G D}
    (hf : IsFeasible (fun _ => 0) f) : value f = 0 := by
  apply le_antisymm _ zero_le
  simpa [weightedEdgeCost] using weak_duality hf hw₀

end
end DirectedFlowCutGap.EdgeFlow
