import Mathlib

/-!
# Directed vertex distances and cuts

Foundations for Section 2.1 of Bodwin–Samborska, arXiv:2604.03412v3.
Paths below are actual finite directed simple paths: an injective sequence of
vertices indexed from `0` to its edge length, with an edge between consecutive
vertices. The length-zero path is included. Both endpoints are excluded from
vertex weights and from the vertices that can cut a path. Weights and costs
are finite nonnegative reals; zero is allowed. Distances take values in
`ENNReal`, so a disconnected pair has distance infinity.

The deletion bridge retains the two endpoints of the demand pair. Deleting
all of `X` is not equivalent to the paper's definition when an endpoint is
in `X`. In particular, this file does not adopt that invalid equivalence.

Pending: conversion of arbitrary walks by loop erasure, distance composition
inequalities, attainment of the infimum, the optimization and algorithmic
claims in Algorithm 2, and the reductions in Theorem 29. No result below
asserts the main flow-cut gap bound.
-/

namespace DirectedFlowCutGap

noncomputable section

open scoped BigOperators NNReal ENNReal

variable {V : Type*}

/-- A directed simple path, represented by its consecutive vertices. -/
structure SimplePath (G : Digraph V) (s t : V) where
  edgeLength : ℕ
  vertex : Fin (edgeLength + 1) → V
  source_eq : vertex 0 = s
  target_eq : vertex (Fin.last edgeLength) = t
  injective : Function.Injective vertex
  adjacent : ∀ i : Fin edgeLength, G.Adj (vertex i.castSucc) (vertex i.succ)

namespace SimplePath

variable {G : Digraph V} {s t : V}

/-- The length-zero path is present even at an isolated vertex. -/
def refl (G : Digraph V) (s : V) : SimplePath G s s where
  edgeLength := 0
  vertex := fun _ => s
  source_eq := rfl
  target_eq := rfl
  injective := by
    intro i j _
    apply Fin.ext
    omega
  adjacent := Fin.elim0

/-- A single directed edge gives a path between distinct vertices. -/
def edge (h : G.Adj s t) (hne : s ≠ t) : SimplePath G s t where
  edgeLength := 1
  vertex := ![s, t]
  source_eq := rfl
  target_eq := rfl
  injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  adjacent := by
    intro i
    fin_cases i
    exact h

variable [DecidableEq V]

/-- Every vertex visited by a path, including its endpoints. -/
def vertices (p : SimplePath G s t) : Finset V := Finset.univ.image p.vertex

/-- Interior vertices, with both endpoints explicitly removed. -/
def internalVertices (p : SimplePath G s t) : Finset V := p.vertices \ {s, t}

@[simp] theorem mem_vertices (p : SimplePath G s t) (v : V) :
    v ∈ p.vertices ↔ ∃ i, p.vertex i = v := by
  simp [vertices]

theorem source_mem_vertices (p : SimplePath G s t) : s ∈ p.vertices :=
  (p.mem_vertices s).mpr ⟨0, p.source_eq⟩

theorem target_mem_vertices (p : SimplePath G s t) : t ∈ p.vertices :=
  (p.mem_vertices t).mpr ⟨Fin.last p.edgeLength, p.target_eq⟩

@[simp] theorem card_vertices (p : SimplePath G s t) :
    p.vertices.card = p.edgeLength + 1 := by
  rw [vertices, Finset.card_image_of_injective _ p.injective]
  simp

theorem edgeLength_lt_card [Fintype V] (p : SimplePath G s t) :
    p.edgeLength < Fintype.card V := by
  have h := Finset.card_le_univ p.vertices
  rw [p.card_vertices] at h
  omega

@[simp] theorem mem_internalVertices (p : SimplePath G s t) (v : V) :
    v ∈ p.internalVertices ↔ (∃ i, p.vertex i = v) ∧ v ≠ s ∧ v ≠ t := by
  simp [internalVertices]

@[simp] theorem source_not_internal (p : SimplePath G s t) :
    s ∉ p.internalVertices := by simp

@[simp] theorem target_not_internal (p : SimplePath G s t) :
    t ∉ p.internalVertices := by simp

@[simp] theorem refl_internalVertices (G : Digraph V) (s : V) :
    (refl G s).internalVertices = ∅ := by
  ext v
  simp [refl, eq_comm]

@[simp] theorem edge_internalVertices (h : G.Adj s t) (hne : s ≠ t) :
    (edge h hne).internalVertices = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨⟨i, rfl⟩, hs, ht⟩ := (mem_internalVertices _ v).mp hv
  fin_cases i <;> simp_all [edge]

/-- The paper's vertex path length counts neither endpoint. -/
def weight (p : SimplePath G s t) (w : V → ℝ≥0) : ℝ≥0 :=
  ∑ v ∈ p.internalVertices, w v

theorem weight_congr (p : SimplePath G s t) {w w' : V → ℝ≥0}
    (h : ∀ v, v ≠ s → v ≠ t → w v = w' v) : p.weight w = p.weight w' := by
  apply Finset.sum_congr rfl
  intro v hv
  obtain ⟨_, hs, ht⟩ := (p.mem_internalVertices v).mp hv
  exact h v hs ht

theorem weight_mono (p : SimplePath G s t) {w w' : V → ℝ≥0}
    (h : ∀ v, w v ≤ w' v) : p.weight w ≤ p.weight w' := by
  exact Finset.sum_le_sum (fun v _ => h v)

@[simp] theorem weight_unit (p : SimplePath G s t) :
    p.weight (fun _ => 1) = (p.internalVertices.card : ℝ≥0) := by
  simp [weight]

@[simp] theorem refl_weight (G : Digraph V) (s : V) (w : V → ℝ≥0) :
    (refl G s).weight w = 0 := by simp [weight]

@[simp] theorem edge_weight (h : G.Adj s t) (hne : s ≠ t) (w : V → ℝ≥0) :
    (edge h hne).weight w = 0 := by simp [weight]

@[simp] theorem weight_zero (p : SimplePath G s t) : p.weight (fun _ => 0) = 0 := by
  simp [weight]

/-- Avoidance concerns internal vertices, even when an endpoint belongs to `X`. -/
def Avoids (p : SimplePath G s t) (X : Finset V) : Prop :=
  ∀ v ∈ p.internalVertices, v ∉ X

end SimplePath

variable [DecidableEq V]

/-- Extended distance, with infinity as the infimum of the empty path family. -/
def vertexDistance (G : Digraph V) (w : V → ℝ≥0) (s t : V) : ℝ≥0∞ :=
  ⨅ p : SimplePath G s t, (p.weight w : ℝ≥0∞)

/-- Threshold distance is exactly the all-path fractional constraint. -/
theorem le_vertexDistance_iff (G : Digraph V) (w : V → ℝ≥0) (s t : V)
    (r : ℝ≥0∞) :
    r ≤ vertexDistance G w s t ↔ ∀ p : SimplePath G s t, r ≤ (p.weight w : ℝ≥0∞) :=
  le_iInf_iff

theorem coe_le_vertexDistance_iff (G : Digraph V) (w : V → ℝ≥0) (s t : V)
    (r : ℝ≥0) :
    (r : ℝ≥0∞) ≤ vertexDistance G w s t ↔ ∀ p : SimplePath G s t, r ≤ p.weight w := by
  simp only [le_vertexDistance_iff, ENNReal.coe_le_coe]

theorem vertexDistance_le_weight {G : Digraph V} (w : V → ℝ≥0) {s t : V}
    (p : SimplePath G s t) : vertexDistance G w s t ≤ (p.weight w : ℝ≥0∞) :=
  iInf_le _ p

theorem vertexDistance_eq_top_iff (G : Digraph V) (w : V → ℝ≥0) (s t : V) :
    vertexDistance G w s t = ⊤ ↔ ¬Nonempty (SimplePath G s t) := by
  constructor
  · intro h ⟨p⟩
    have hp := vertexDistance_le_weight w p
    rw [h] at hp
    exact ENNReal.coe_ne_top (top_le_iff.mp hp)
  · intro h
    apply top_unique
    rw [le_vertexDistance_iff]
    intro p
    exact (h ⟨p⟩).elim

@[simp] theorem vertexDistance_self (G : Digraph V) (w : V → ℝ≥0) (s : V) :
    vertexDistance G w s s = 0 := by
  apply le_antisymm _ bot_le
  simpa using vertexDistance_le_weight w (SimplePath.refl G s)

theorem vertexDistance_of_adj {G : Digraph V} (w : V → ℝ≥0) {s t : V}
    (h : G.Adj s t) : vertexDistance G w s t = 0 := by
  by_cases hst : s = t
  · subst t
    exact vertexDistance_self G w s
  · apply le_antisymm _ bot_le
    simpa using vertexDistance_le_weight w (SimplePath.edge h hst)

theorem vertexDistance_congr_endpoints (G : Digraph V) {w w' : V → ℝ≥0} (s t : V)
    (h : ∀ v, v ≠ s → v ≠ t → w v = w' v) :
    vertexDistance G w s t = vertexDistance G w' s t := by
  apply iInf_congr
  intro p
  rw [p.weight_congr h]

theorem vertexDistance_mono (G : Digraph V) {w w' : V → ℝ≥0} (s t : V)
    (h : ∀ v, w v ≤ w' v) : vertexDistance G w s t ≤ vertexDistance G w' s t := by
  exact iInf_mono fun p => ENNReal.coe_le_coe.mpr (p.weight_mono h)

/-- An integral vertex cut must meet every path at an internal vertex. -/
def CutsPair (G : Digraph V) (X : Finset V) (s t : V) : Prop :=
  ∀ p : SimplePath G s t, ∃ v ∈ p.internalVertices, v ∈ X

theorem not_cutsPair_iff (G : Digraph V) (X : Finset V) (s t : V) :
    ¬CutsPair G X s t ↔ ∃ p : SimplePath G s t, p.Avoids X := by
  simp only [CutsPair, SimplePath.Avoids, not_forall, not_exists, not_and]

/-- Cutting an endpoint contributes nothing to cutting its demand pair. -/
theorem cutsPair_erase_endpoints_iff (G : Digraph V) (X : Finset V) (s t : V) :
    CutsPair G ((X.erase s).erase t) s t ↔ CutsPair G X s t := by
  constructor
  · intro h p
    obtain ⟨v, hv, hx⟩ := h p
    exact ⟨v, hv, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)⟩
  · intro h p
    obtain ⟨v, hv, hx⟩ := h p
    obtain ⟨_, hs, ht⟩ := (p.mem_internalVertices v).mp hv
    exact ⟨v, hv, by simp [hs, ht, hx]⟩

/-- Even selecting both endpoints fails to cut any existing path. -/
theorem not_cutsPair_subset_endpoints {G : Digraph V} {s t : V}
    (p : SimplePath G s t) {X : Finset V} (hX : X ⊆ {s, t}) :
    ¬CutsPair G X s t := by
  intro h
  obtain ⟨v, hv, hx⟩ := h p
  obtain ⟨_, hs, ht⟩ := (p.mem_internalVertices v).mp hv
  have he := hX hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  exact he.elim hs ht

theorem cutsPair_mono {G : Digraph V} {X Y : Finset V} {s t : V}
    (hXY : X ⊆ Y) (h : CutsPair G X s t) : CutsPair G Y s t := by
  intro p
  obtain ⟨v, hv, hx⟩ := h p
  exact ⟨v, hv, hXY hx⟩

theorem not_cutsPair_self (G : Digraph V) (X : Finset V) (s : V) :
    ¬CutsPair G X s s := by
  intro h
  simpa using h (SimplePath.refl G s)

theorem not_cutsPair_of_adj {G : Digraph V} (X : Finset V) {s t : V}
    (h : G.Adj s t) : ¬CutsPair G X s t := by
  by_cases hst : s = t
  · subst t
    exact not_cutsPair_self G X s
  · intro hc
    simpa using hc (SimplePath.edge h hst)

/-- Fractional feasibility for an explicitly given family of demand pairs. -/
def IsFractionalCut (G : Digraph V) (w : V → ℝ≥0) (D : Set (V × V)) : Prop :=
  ∀ s t, (s, t) ∈ D → 1 ≤ vertexDistance G w s t

/-- Integral feasibility for an explicitly given family of demand pairs. -/
def IsIntegralCut (G : Digraph V) (X : Finset V) (D : Set (V × V)) : Prop :=
  ∀ s t, (s, t) ∈ D → CutsPair G X s t

theorem isFractionalCut_iff (G : Digraph V) (w : V → ℝ≥0) (D : Set (V × V)) :
    IsFractionalCut G w D ↔
      ∀ s t, (s, t) ∈ D → ∀ p : SimplePath G s t, 1 ≤ p.weight w := by
  simp only [IsFractionalCut, ← ENNReal.coe_one, coe_le_vertexDistance_iff]

/-- The demand set implicit in the statement of the paper's vertex theorems. -/
def thresholdDemands (G : Digraph V) (w : V → ℝ≥0) : Set (V × V) :=
  {st | 1 ≤ vertexDistance G w st.1 st.2}

theorem isFractionalCut_thresholdDemands (G : Digraph V) (w : V → ℝ≥0) :
    IsFractionalCut G w (thresholdDemands G w) := by
  intro s t h
  exact h

/-- Retain each demand endpoint even if it is selected in the cut. -/
def Retained (X : Finset V) (s t v : V) : Prop := v ∉ X ∨ v = s ∨ v = t

theorem retained_iff_not_mem_erase (X : Finset V) (s t v : V) :
    Retained X s t v ↔ v ∉ (X.erase s).erase t := by
  simp only [Retained, Finset.mem_erase]
  tauto

/-- The induced graph on `V \ (X \ {s,t})`, with an actual restricted vertex type. -/
def endpointDeletedGraph (G : Digraph V) (X : Finset V) (s t : V) :
    Digraph {v : V // Retained X s t v} where
  Adj u v := G.Adj u.val v.val

def retainedSource (X : Finset V) (s t : V) : {v : V // Retained X s t v} :=
  ⟨s, Or.inr (Or.inl rfl)⟩

def retainedTarget (X : Finset V) (s t : V) : {v : V // Retained X s t v} :=
  ⟨t, Or.inr (Or.inr rfl)⟩

namespace SimplePath

variable {G : Digraph V} {s t : V}

theorem avoids_iff_retained (p : SimplePath G s t) (X : Finset V) :
    p.Avoids X ↔ ∀ i, Retained X s t (p.vertex i) := by
  constructor
  · intro h i
    by_cases hs : p.vertex i = s
    · exact Or.inr (Or.inl hs)
    by_cases ht : p.vertex i = t
    · exact Or.inr (Or.inr ht)
    exact Or.inl (h _ ((p.mem_internalVertices _).mpr ⟨⟨i, rfl⟩, hs, ht⟩))
  · intro h v hv hx
    obtain ⟨⟨i, hi⟩, hs, ht⟩ := (p.mem_internalVertices v).mp hv
    have hr := h i
    rw [hi] at hr
    rcases hr with hn | he | he
    · exact hn hx
    · exact hs he
    · exact ht he

/-- An avoiding path lifts to the actual induced graph with endpoints retained. -/
def liftAvoiding (p : SimplePath G s t) (X : Finset V) (h : p.Avoids X) :
    SimplePath (endpointDeletedGraph G X s t) (retainedSource X s t)
      (retainedTarget X s t) where
  edgeLength := p.edgeLength
  vertex i := ⟨p.vertex i, (p.avoids_iff_retained X).mp h i⟩
  source_eq := Subtype.ext p.source_eq
  target_eq := Subtype.ext p.target_eq
  injective := by
    intro i j hij
    exact p.injective (congrArg Subtype.val hij)
  adjacent := p.adjacent

/-- Forget the induced-graph subtype without changing any path vertex. -/
def forgetDeletion {X : Finset V}
    (p : SimplePath (endpointDeletedGraph G X s t) (retainedSource X s t)
      (retainedTarget X s t)) : SimplePath G s t where
  edgeLength := p.edgeLength
  vertex i := (p.vertex i).val
  source_eq := congrArg Subtype.val p.source_eq
  target_eq := congrArg Subtype.val p.target_eq
  injective := by
    intro i j hij
    exact p.injective (Subtype.ext hij)
  adjacent := p.adjacent

theorem forgetDeletion_avoids {X : Finset V}
    (p : SimplePath (endpointDeletedGraph G X s t) (retainedSource X s t)
      (retainedTarget X s t)) : p.forgetDeletion.Avoids X := by
  apply (p.forgetDeletion.avoids_iff_retained X).mpr
  intro i
  exact (p.vertex i).property

end SimplePath

/-- Exact path correspondence for endpoint-preserving deletion. -/
theorem endpointDeletedGraph_path_iff (G : Digraph V) (X : Finset V) (s t : V) :
    Nonempty (SimplePath (endpointDeletedGraph G X s t) (retainedSource X s t)
      (retainedTarget X s t)) ↔ ∃ p : SimplePath G s t, p.Avoids X := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.forgetDeletion, p.forgetDeletion_avoids⟩
  · rintro ⟨p, hp⟩
    exact ⟨p.liftAvoiding X hp⟩

/-- A pair is cut exactly when the graph with only its internal cut vertices
deleted has no path between its retained endpoints. -/
theorem cutsPair_iff_endpointDeletedGraph (G : Digraph V) (X : Finset V) (s t : V) :
    CutsPair G X s t ↔
      ¬Nonempty (SimplePath (endpointDeletedGraph G X s t) (retainedSource X s t)
        (retainedTarget X s t)) := by
  rw [endpointDeletedGraph_path_iff, ← not_cutsPair_iff, not_not]

/-- The cost of a vertex cut, with nonnegative costs and zero costs allowed. -/
def cutCost (cost : V → ℝ≥0) (X : Finset V) : ℝ≥0 := ∑ v ∈ X, cost v

variable [Fintype V]

/-- Total vertex weight `w(V)`. -/
def totalWeight (w : V → ℝ≥0) : ℝ≥0 := ∑ v, w v

/-- Fractional cut objective `⟨cost,w⟩`. -/
def weightedCost (cost w : V → ℝ≥0) : ℝ≥0 := ∑ v, cost v * w v

omit [DecidableEq V] in
@[simp] theorem weightedCost_unit (w : V → ℝ≥0) :
    weightedCost (fun _ => 1) w = totalWeight w := by
  simp [weightedCost, totalWeight]

omit [DecidableEq V] [Fintype V] in
@[simp] theorem cutCost_unit (X : Finset V) :
    cutCost (fun _ => 1) X = (X.card : ℝ≥0) := by
  simp [cutCost]

end

end DirectedFlowCutGap
