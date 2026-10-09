import DirectedFlowCutGap.Basic
import DirectedFlowCutGap.PathExtraction
import DirectedFlowCutGap.PackingCovering

/-!
# Directed vertex sum-multiflow duality

The finite packing coordinates in this file are actual directed simple paths,
indexed by their demand pair. A vertex load counts only internal vertices, just
as `SimplePath.weight` and `IsFractionalCut` do. Path amounts and capacities are
nonnegative reals, including zero. The objective is the sum of all path amounts;
there is no prescribed common throughput for different demands.

An actual feasible fractional cut is the only domain hypothesis for the attained
duality theorem. It implies that no demand path has an empty interior. Empty
demand sets and unreachable pairs produce no packing coordinates, and need no
extra assumptions. Conversely, a demand with an empty-interior path has no
feasible fractional cut under the endpoint-excluding convention.

This identifies the graph optimization problems with finite packing/covering.
It makes no flow-cut-gap or algorithmic running-time claim.
-/

namespace DirectedFlowCutGap.VertexFlow

noncomputable section
open scoped BigOperators NNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every coordinate is a genuine path for a genuine demand in `D`. -/
abbrev PathIndex (G : Digraph V) (D : Set (V × V)) :=
  Σ st : D, SimplePath G st.val.1 st.val.2

/-- Finiteness follows from finite coding of actual simple paths. -/
instance pathIndexFintype (G : Digraph V) (D : Set (V × V)) :
    Fintype (PathIndex G D) := Fintype.ofFinite _

variable {G : Digraph V} {D : Set (V × V)}

/-- Endpoints are excluded from the resources consumed by each path. -/
def resources (p : PathIndex G D) : Finset V := p.2.internalVertices

/-- A sum-multiflow assigns a nonnegative amount to each actual demand path. -/
abbrev Flow (G : Digraph V) (D : Set (V × V)) := PathIndex G D → ℝ≥0

/-- Total flow through a vertex as an internal vertex. -/
def load (f : Flow G D) (v : V) : ℝ≥0 := by
  classical
  exact ∑ p with v ∈ resources p, f p

/-- The total amount routed across all demands, with no concurrency constraint. -/
def value (f : Flow G D) : ℝ≥0 := ∑ p, f p

/-- Amounts are nonnegative by their type; all vertex capacities must hold. -/
def IsFeasible (capacity : V → ℝ≥0) (f : Flow G D) : Prop :=
  ∀ v, load f v ≤ capacity v

/-- The real incidence load is exactly the coercion of the graph vertex load. -/
theorem incidence_load_eq (f : Flow G D) (v : V) :
    PackingCovering.load resources (fun p => (f p : ℝ)) v = (load f v : ℝ) := by
  classical
  rw [PackingCovering.load_eq_sum_filter]
  simp [load, NNReal.coe_sum]

/-- The covering path constraint uses exactly the path weight from `Basic`. -/
theorem incidence_pathWeight_eq (w : V → ℝ≥0) (p : PathIndex G D) :
    PackingCovering.pathWeight resources (fun v => (w v : ℝ)) p =
      (p.2.weight w : ℝ) := by
  rw [PackingCovering.pathWeight_eq_sum]
  simp [resources, SimplePath.weight, NNReal.coe_sum]

/-- The finite packing objective is the real coercion of total routed amount. -/
theorem packingValue_eq (f : Flow G D) :
    PackingCovering.packingValue (fun p => (f p : ℝ)) = (value f : ℝ) := by
  simp [PackingCovering.packingValue, value, NNReal.coe_sum]

omit [DecidableEq V] in
/-- The finite covering objective is the capacity-weighted cut cost from `Basic`. -/
theorem coveringValue_eq (capacity w : V → ℝ≥0) :
    PackingCovering.coveringValue (fun v => (capacity v : ℝ))
      (fun v => (w v : ℝ)) = (weightedCost capacity w : ℝ) := by
  simp [PackingCovering.coveringValue, weightedCost, NNReal.coe_sum, NNReal.coe_mul]

/-- Exact feasibility identification, including every real/nonnegative-real cast. -/
theorem isPacking_iff (capacity : V → ℝ≥0) (f : Flow G D) :
    PackingCovering.IsPacking resources (fun v => (capacity v : ℝ))
      (fun p => (f p : ℝ)) ↔ IsFeasible capacity f := by
  constructor
  · intro hf v
    apply NNReal.coe_le_coe.mp
    rw [← incidence_load_eq]
    exact hf.2 v
  · intro hf
    refine ⟨fun p => (f p).coe_nonneg, fun v => ?_⟩
    rw [incidence_load_eq]
    exact NNReal.coe_le_coe.mpr (hf v)

/-- Exact equivalence with the all-demand distance definition of fractional cut. -/
theorem isCovering_iff (w : V → ℝ≥0) :
    PackingCovering.IsCovering (resources (G := G) (D := D))
      (fun v => (w v : ℝ)) ↔ IsFractionalCut G w D := by
  rw [isFractionalCut_iff]
  constructor
  · intro hw s t hst p
    have h := hw.2 (⟨⟨(s, t), hst⟩, p⟩ : PathIndex G D)
    rw [incidence_pathWeight_eq] at h
    exact NNReal.one_le_coe.mp h
  · intro hw
    refine ⟨fun v => (w v).coe_nonneg, ?_⟩
    intro p
    rw [incidence_pathWeight_eq]
    exact NNReal.one_le_coe.mpr (hw _ _ p.1.property p.2)

omit [Fintype V] in
/-- Feasible cut weights exclude every zero-resource path. -/
theorem resources_nonempty_of_fractionalCut {w : V → ℝ≥0}
    (hw : IsFractionalCut G w D) (p : PathIndex G D) :
    (resources p).Nonempty := by
  have hp := (isFractionalCut_iff G w D).mp hw _ _ p.1.property p.2
  by_contra hempty
  have he : p.2.internalVertices = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  simp [SimplePath.weight, he] at hp

omit [Fintype V] in
/-- Precise feasible-cut domain: every actual demand path has an internal vertex.
The reverse implication constructs the unit vertex weighting. -/
theorem exists_fractionalCut_iff :
    (∃ w : V → ℝ≥0, IsFractionalCut G w D) ↔
      ∀ p : PathIndex G D, (resources p).Nonempty := by
  constructor
  · rintro ⟨w, hw⟩
    exact resources_nonempty_of_fractionalCut hw
  · intro h
    refine ⟨fun _ => 1, (isFractionalCut_iff G _ D).mpr ?_⟩
    intro s t hst p
    have hp := h (⟨⟨(s, t), hst⟩, p⟩ : PathIndex G D)
    rw [SimplePath.weight_unit]
    exact Nat.one_le_cast.mpr (Finset.card_pos.mpr hp)

omit [Fintype V] in
/-- A zero-interior demand path makes the fractional-cut problem infeasible. -/
theorem no_fractionalCut_of_empty_resources (p : PathIndex G D)
    (hp : resources p = ∅) : ¬ ∃ w : V → ℝ≥0, IsFractionalCut G w D := by
  rw [exists_fractionalCut_iff]
  intro h
  simpa [hp] using h p

omit [Fintype V] in
/-- A diagonal demand is outside the feasible-cut domain. -/
theorem no_fractionalCut_of_self {s : V} (hs : (s, s) ∈ D) :
    ¬ ∃ w : V → ℝ≥0, IsFractionalCut G w D := by
  apply no_fractionalCut_of_empty_resources
    (⟨⟨(s, s), hs⟩, SimplePath.refl G s⟩ : PathIndex G D)
  simp [resources]

omit [Fintype V] in
/-- A demand joined by a directed edge is outside the feasible-cut domain. -/
theorem no_fractionalCut_of_adj {s t : V} (hst : (s, t) ∈ D) (hadj : G.Adj s t) :
    ¬ ∃ w : V → ℝ≥0, IsFractionalCut G w D := by
  rintro ⟨w, hw⟩
  have h := hw s t hst
  simp [vertexDistance_of_adj w hadj] at h

/-- Graph weak duality follows by exact identification with finite incidence LPs. -/
theorem weak_duality {capacity w : V → ℝ≥0} {f : Flow G D}
    (hf : IsFeasible capacity f) (hw : IsFractionalCut G w D) :
    value f ≤ weightedCost capacity w := by
  have h := PackingCovering.weak_duality resources
    ((isPacking_iff capacity f).mpr hf) ((isCovering_iff w).mpr hw)
  rw [packingValue_eq, coveringValue_eq] at h
  exact NNReal.coe_le_coe.mp h

/-- An attained maximum directed vertex sum-multiflow and an attained minimum
fractional vertex cut have equal objectives. The supplied `w₀` is only a feasible
cut, and need not be optimal. Zero capacities and empty path families are allowed.
The minimum cut can be chosen with every weight at most one. -/
theorem strong_duality (capacity w₀ : V → ℝ≥0) (hw₀ : IsFractionalCut G w₀ D) :
    ∃ (f : Flow G D) (w : V → ℝ≥0),
      IsFeasible capacity f ∧ IsFractionalCut G w D ∧
      value f = weightedCost capacity w ∧
      (∀ g : Flow G D, IsFeasible capacity g → value g ≤ value f) ∧
      (∀ z : V → ℝ≥0, IsFractionalCut G z D →
        weightedCost capacity w ≤ weightedCost capacity z) ∧
      (∀ v, w v ≤ 1) := by
  classical
  obtain ⟨fr, wr, hfr, hwr, heq, hmax, hmin, hwr1⟩ :=
    PackingCovering.strong_duality (resources (G := G) (D := D))
      (fun v => (capacity v).coe_nonneg) (resources_nonempty_of_fractionalCut hw₀)
  let f : Flow G D := fun p => ⟨fr p, hfr.1 p⟩
  let w : V → ℝ≥0 := fun v => ⟨wr v, hwr.1 v⟩
  have hf : IsFeasible capacity f := (isPacking_iff capacity f).mp hfr
  have hw : IsFractionalCut G w D := (isCovering_iff w).mp hwr
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
  · intro v
    exact NNReal.coe_le_one.mp (hwr1 v)

omit [Fintype V] [DecidableEq V] in
/-- Unreachable demands contribute no path coordinates at all. -/
theorem isEmpty_pathIndex_iff :
    IsEmpty (PathIndex G D) ↔
      ∀ s t, (s, t) ∈ D → ¬ Nonempty (SimplePath G s t) := by
  constructor
  · intro h s t hst hp
    exact h.false ⟨⟨(s, t), hst⟩, hp.some⟩
  · intro h
    exact ⟨fun p => h _ _ p.1.property ⟨p.2⟩⟩

/-- If every demanded pair is unreachable, every flow has value zero. -/
theorem value_eq_zero_of_unreachable
    (h : ∀ s t, (s, t) ∈ D → ¬ Nonempty (SimplePath G s t)) (f : Flow G D) :
    value f = 0 := by
  let : IsEmpty (PathIndex G D) := isEmpty_pathIndex_iff.mpr h
  simp [value]

omit [Fintype V] in
/-- A zero fractional cut suffices when all demands are unreachable. -/
theorem zero_isFractionalCut_of_unreachable
    (h : ∀ s t, (s, t) ∈ D → ¬ Nonempty (SimplePath G s t)) :
    IsFractionalCut G (fun _ => 0) D := by
  rw [isFractionalCut_iff]
  intro s t hst p
  exact (h s t hst ⟨p⟩).elim

omit [Fintype V] in
/-- The empty demand set has a feasible zero cut. -/
theorem zero_isFractionalCut_empty (G : Digraph V) :
    IsFractionalCut G (fun _ => 0) ∅ := by
  intro s t hst
  exact hst.elim

/-- With no demands, there is no routed amount. -/
theorem value_eq_zero_empty (f : Flow G ∅) : value f = 0 :=
  value_eq_zero_of_unreachable (fun _ _ h => h.elim) f

/-- On the feasible-cut domain, zero capacities force total routed amount zero. -/
theorem value_eq_zero_of_zero_capacity {w₀ : V → ℝ≥0}
    (hw₀ : IsFractionalCut G w₀ D) {f : Flow G D}
    (hf : IsFeasible (fun _ => 0) f) : value f = 0 := by
  apply le_antisymm _ zero_le
  simpa [weightedCost] using weak_duality hf hw₀

end
end DirectedFlowCutGap.VertexFlow
