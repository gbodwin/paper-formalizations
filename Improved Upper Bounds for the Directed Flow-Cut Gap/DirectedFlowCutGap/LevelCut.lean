import DirectedFlowCutGap.PathExtraction

/-!
# Deterministic level-cut geometry

The level cut is the actual set of vertices whose closed distance interval
contains the sampled level. Distances remain in `ENNReal`: an unreachable vertex
is never selected at a finite level. The adjacent-crossing argument below is
proved from the indexed vertices of each actual directed simple path.

`levelCut_source_or_cutsPair` is Lemma 11 of Bodwin–Samborska,
arXiv:2604.03412v3. `levelCut_cuts_source_demand` supplies the single-round
geometric step of Lemma 12, including the upper boundary `d = 1`. The theorem
`levelCut_cuts_source_demand_unit` also handles the lower boundary `d = 0`.
These do not
claim the separate iteration/termination invariant of the whole algorithm.
The interval-length lemmas at the end are deterministic; no sampling law or
expectation identity is assumed here.
-/

namespace DirectedFlowCutGap

noncomputable section

open scoped NNReal ENNReal

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The closed level interval used by Algorithm 2. The level is finite. -/
def levelCut (G : Digraph V) (w : V → ℝ≥0) (s : V) (d : ℝ≥0) : Finset V :=
  Finset.univ.filter fun v =>
    vertexDistance G w s v ≤ (d : ℝ≥0∞) ∧
      (d : ℝ≥0∞) ≤ vertexDistance G w s v + (w v : ℝ≥0∞)

@[simp] theorem mem_levelCut (G : Digraph V) (w : V → ℝ≥0) (s v : V)
    (d : ℝ≥0) :
    v ∈ levelCut G w s d ↔
      vertexDistance G w s v ≤ (d : ℝ≥0∞) ∧
        (d : ℝ≥0∞) ≤ vertexDistance G w s v + (w v : ℝ≥0∞) := by
  simp [levelCut]

/-- Unreachable vertices cannot be selected by any finite level. -/
theorem not_mem_levelCut_of_distance_top {G : Digraph V} {w : V → ℝ≥0}
    {s v : V} (h : vertexDistance G w s v = ⊤) (d : ℝ≥0) :
    v ∉ levelCut G w s d := by
  simp [mem_levelCut, h]

/-- The local vertex-distance inequality charges the tail of an edge. -/
theorem vertexDistance_le_of_adj (G : Digraph V) (w : V → ℝ≥0) (s : V)
    {u v : V} (h : G.Adj u v) :
    vertexDistance G w s v ≤ vertexDistance G w s u + (w u : ℝ≥0∞) := by
  simpa [vertexDistance_of_adj w h] using vertexDistance_triangle G w s u v

/-- Finite distance propagates along an actual path, even when other pairs
in the graph are unreachable. -/
theorem vertexDistance_lt_top_of_path {G : Digraph V} (w : V → ℝ≥0)
    {s u v : V} (hu : vertexDistance G w s u < ⊤) (p : SimplePath G u v) :
    vertexDistance G w s v < ⊤ := by
  have huv : vertexDistance G w u v < ⊤ :=
    lt_of_le_of_lt (vertexDistance_le_weight w p) ENNReal.coe_lt_top
  exact lt_of_le_of_lt (vertexDistance_triangle G w s u v)
    (ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hu, huv⟩,
      ENNReal.coe_lt_top⟩)

namespace SimplePath

variable {G : Digraph V} {u v : V}

omit [DecidableEq V] [Fintype V] in
/-- A predicate true at the first indexed vertex and false at the last must
change from true to false across an actual edge of this path. -/
theorem exists_adjacent_break (p : SimplePath G u v) (P : V → Prop)
    (hu : P u) (hv : ¬P v) :
    ∃ i : Fin p.edgeLength, P (p.vertex i.castSucc) ∧ ¬P (p.vertex i.succ) := by
  classical
  by_contra h
  have hstep : ∀ i : Fin p.edgeLength,
      P (p.vertex i.castSucc) → P (p.vertex i.succ) := by
    intro i hi
    by_contra hnext
    exact h ⟨i, hi, hnext⟩
  have hall : ∀ i : Fin (p.edgeLength + 1), P (p.vertex i) := by
    intro i
    induction i using Fin.induction with
    | zero => simpa [p.source_eq] using hu
    | succ i hi => exact hstep i hi
  exact hv (by simpa [p.target_eq] using hall (Fin.last p.edgeLength))

omit [DecidableEq V] [Fintype V] in
/-- Every indexed vertex strictly before the last differs from the target. -/
theorem castSucc_vertex_ne_target (p : SimplePath G u v) (i : Fin p.edgeLength) :
    p.vertex i.castSucc ≠ v := by
  intro h
  have hi := congrArg Fin.val (p.injective (h.trans p.target_eq.symm))
  have hil := i.isLt
  simp only [Fin.val_castSucc, Fin.val_last] at hi
  omega

omit [Fintype V] in
/-- A crossing from at most the level to strictly above it. -/
theorem exists_levelCrossing (p : SimplePath G u v) (w : V → ℝ≥0)
    (s : V) (d : ℝ≥0)
    (hu : vertexDistance G w s u ≤ (d : ℝ≥0∞))
    (hv : (d : ℝ≥0∞) < vertexDistance G w s v) :
    ∃ i : Fin p.edgeLength,
      vertexDistance G w s (p.vertex i.castSucc) ≤ (d : ℝ≥0∞) ∧
      (d : ℝ≥0∞) < vertexDistance G w s (p.vertex i.succ) := by
  obtain ⟨i, hi, hj⟩ := p.exists_adjacent_break
    (fun x => vertexDistance G w s x ≤ (d : ℝ≥0∞)) hu (not_le.mpr hv)
  exact ⟨i, hi, not_le.mp hj⟩

omit [Fintype V] in
/-- The complementary crossing convention allows equality at the upper
endpoint, and is used for the sampled boundary `d = 1`. -/
theorem exists_levelCrossing_closed (p : SimplePath G u v) (w : V → ℝ≥0)
    (s : V) (d : ℝ≥0)
    (hu : vertexDistance G w s u < (d : ℝ≥0∞))
    (hv : (d : ℝ≥0∞) ≤ vertexDistance G w s v) :
    ∃ i : Fin p.edgeLength,
      vertexDistance G w s (p.vertex i.castSucc) < (d : ℝ≥0∞) ∧
      (d : ℝ≥0∞) ≤ vertexDistance G w s (p.vertex i.succ) := by
  obtain ⟨i, hi, hj⟩ := p.exists_adjacent_break
    (fun x => vertexDistance G w s x < (d : ℝ≥0∞)) hu (not_lt.mpr hv)
  exact ⟨i, hi, not_lt.mp hj⟩

end SimplePath

/-- The tail of an edge spanning the level is selected. -/
theorem mem_levelCut_of_crossing {G : Digraph V} (w : V → ℝ≥0)
    (s : V) (d : ℝ≥0) {u v : V} (hadj : G.Adj u v)
    (hu : vertexDistance G w s u ≤ (d : ℝ≥0∞))
    (hv : (d : ℝ≥0∞) ≤ vertexDistance G w s v) :
    u ∈ levelCut G w s d := by
  exact (mem_levelCut G w s u d).mpr
    ⟨hu, hv.trans (vertexDistance_le_of_adj G w s hadj)⟩

/-- Lemma 11: the level cut contains `u`, or meets every actual `u → v`
simple path internally. Neither endpoint alone counts as cutting a path. -/
theorem levelCut_source_or_cutsPair (G : Digraph V) (w : V → ℝ≥0)
    (s : V) (d : ℝ≥0) {u v : V}
    (hu : vertexDistance G w s u ≤ (d : ℝ≥0∞))
    (hv : (d : ℝ≥0∞) < vertexDistance G w s v) :
    u ∈ levelCut G w s d ∨ CutsPair G (levelCut G w s d) u v := by
  by_cases huX : u ∈ levelCut G w s d
  · exact Or.inl huX
  · right
    intro p
    obtain ⟨i, hi, hj⟩ := p.exists_levelCrossing w s d hu hv
    have hx := mem_levelCut_of_crossing w s d (p.adjacent i) hi hj.le
    refine ⟨p.vertex i.castSucc, ?_, hx⟩
    apply (p.mem_internalVertices _).mpr
    exact ⟨⟨i.castSucc, rfl⟩, fun h => huX (h ▸ hx), p.castSucc_vertex_ne_target i⟩

/-- The Lemma 11 conclusion remains true after adding the level cut to an
already accumulated set of selected vertices. -/
theorem source_or_cutsPair_of_levelCut_subset (G : Digraph V) (w : V → ℝ≥0)
    (s : V) (d : ℝ≥0) {u v : V} {X : Finset V}
    (hX : levelCut G w s d ⊆ X)
    (hu : vertexDistance G w s u ≤ (d : ℝ≥0∞))
    (hv : (d : ℝ≥0∞) < vertexDistance G w s v) :
    u ∈ X ∨ CutsPair G X u v := by
  rcases levelCut_source_or_cutsPair G w s d hu hv with h | h
  · exact Or.inl (hX h)
  · exact Or.inr (cutsPair_mono hX h)

omit [Fintype V] in
/-- A feasible demand cannot be a self demand. -/
theorem ne_of_one_le_vertexDistance {G : Digraph V} {w : V → ℝ≥0}
    {s t : V} (h : 1 ≤ vertexDistance G w s t) : s ≠ t := by
  rintro rfl
  simp at h

omit [Fintype V] in
/-- A feasible demand cannot consist of a direct edge, because both path
endpoints are excluded from its weight. -/
theorem not_adj_of_one_le_vertexDistance {G : Digraph V} {w : V → ℝ≥0}
    {s t : V} (h : 1 ≤ vertexDistance G w s t) : ¬G.Adj s t := by
  intro hadj
  simp [vertexDistance_of_adj w hadj] at h

/-- Single-round geometric correctness for Lemma 12, with the upper sampled
boundary included. The crossing vertex cannot be the source: its successor
would have distance zero, contradicting the positive sampled level.
Unreachable demands are included, since `CutsPair` quantifies actual paths. -/
theorem levelCut_cuts_source_demand (G : Digraph V) (w : V → ℝ≥0)
    {s t : V} (hst : 1 ≤ vertexDistance G w s t)
    (d : ℝ≥0) (hd0 : 0 < d) (hd1 : d ≤ 1) :
    CutsPair G (levelCut G w s d) s t := by
  intro p
  have hd0' : (0 : ℝ≥0∞) < (d : ℝ≥0∞) := by exact_mod_cast hd0
  have hd1' : (d : ℝ≥0∞) ≤ 1 := by exact_mod_cast hd1
  obtain ⟨i, hi, hj⟩ := p.exists_levelCrossing_closed w s d
    (by simpa using hd0') (hd1'.trans hst)
  have hx := mem_levelCut_of_crossing w s d (p.adjacent i) hi.le hj
  have hsource : p.vertex i.castSucc ≠ s := by
    intro heq
    have hadj : G.Adj s (p.vertex i.succ) := by simpa [heq] using p.adjacent i
    have hz : vertexDistance G w s (p.vertex i.succ) = 0 :=
      vertexDistance_of_adj w hadj
    exact (not_le_of_gt hd0') (by simpa [hz] using hj)
  exact ⟨p.vertex i.castSucc,
    (p.mem_internalVertices _).mpr
      ⟨⟨i.castSucc, rfl⟩, hsource, p.castSucc_vertex_ne_target i⟩, hx⟩

/-- The open-interval formulation used for a uniform sample away from its
two endpoints. -/
theorem levelCut_cuts_source_demand_open (G : Digraph V) (w : V → ℝ≥0)
    {s t : V} (hst : 1 ≤ vertexDistance G w s t)
    (d : ℝ≥0) (hd0 : 0 < d) (hd1 : d < 1) :
    CutsPair G (levelCut G w s d) s t :=
  levelCut_cuts_source_demand G w hst d hd0 hd1.le

/-- The lower sampled boundary is also safe. Use a zero-distance vertex
before a positive-distance successor; that vertex cannot be the source. -/
theorem levelCut_cuts_source_demand_zero (G : Digraph V) (w : V → ℝ≥0)
    {s t : V} (hst : 1 ≤ vertexDistance G w s t) :
    CutsPair G (levelCut G w s 0) s t := by
  intro p
  obtain ⟨i, hi, hj⟩ := p.exists_levelCrossing w s 0
    (by simp) (lt_of_lt_of_le zero_lt_one hst)
  have hx := mem_levelCut_of_crossing w s 0 (p.adjacent i) hi hj.le
  have hsource : p.vertex i.castSucc ≠ s := by
    intro heq
    have hadj : G.Adj s (p.vertex i.succ) := by simpa [heq] using p.adjacent i
    have hz : vertexDistance G w s (p.vertex i.succ) = 0 :=
      vertexDistance_of_adj w hadj
    simp [hz] at hj
  exact ⟨p.vertex i.castSucc,
    (p.mem_internalVertices _).mpr
      ⟨⟨i.castSucc, rfl⟩, hsource, p.castSucc_vertex_ne_target i⟩, hx⟩

/-- All levels in the closed sampling interval `[0,1]` cut the selected
feasible source demand, with no probability-zero endpoint exceptions. -/
theorem levelCut_cuts_source_demand_unit (G : Digraph V) (w : V → ℝ≥0)
    {s t : V} (hst : 1 ≤ vertexDistance G w s t)
    (d : ℝ≥0) (hd1 : d ≤ 1) :
    CutsPair G (levelCut G w s d) s t := by
  by_cases hd0 : d = 0
  · subst d
    exact levelCut_cuts_source_demand_zero G w hst
  · exact levelCut_cuts_source_demand G w hst d (pos_iff_ne_zero.mpr hd0) hd1

/-- Any fractionally feasible selected demand is cut in its own round. -/
theorem IsFractionalCut.levelCut_cuts_selected {G : Digraph V} {w : V → ℝ≥0}
    {D : Set (V × V)} (hw : IsFractionalCut G w D) {s t : V}
    (hst : (s, t) ∈ D) (d : ℝ≥0) (hd0 : 0 < d) (hd1 : d ≤ 1) :
    CutsPair G (levelCut G w s d) s t :=
  levelCut_cuts_source_demand G w (hw s t hst) d hd0 hd1

/-- Fractional feasibility supplies the closed-interval version as well. -/
theorem IsFractionalCut.levelCut_cuts_selected_unit {G : Digraph V} {w : V → ℝ≥0}
    {D : Set (V × V)} (hw : IsFractionalCut G w D) {s t : V}
    (hst : (s, t) ∈ D) (d : ℝ≥0) (hd1 : d ≤ 1) :
    CutsPair G (levelCut G w s d) s t :=
  levelCut_cuts_source_demand_unit G w (hw s t hst) d hd1

/-- Selection at a finite distance is exactly membership of its finite closed
interval. This theorem is unavailable for infinite distances by design. -/
theorem mem_levelCut_iff_of_distance_ne_top (G : Digraph V) (w : V → ℝ≥0)
    (s v : V) (d : ℝ≥0) (h : vertexDistance G w s v ≠ ⊤) :
    v ∈ levelCut G w s d ↔
      (vertexDistance G w s v).toNNReal ≤ d ∧
        d ≤ (vertexDistance G w s v).toNNReal + w v := by
  rw [mem_levelCut, ← ENNReal.coe_toNNReal h, ← ENNReal.coe_add]
  simp only [ENNReal.coe_le_coe, ENNReal.toNNReal_coe]

/-- On the sampling interval, the finite-distance selection event is exactly
the closed interval whose endpoint difference is used below. -/
theorem mem_levelCut_unit_iff (G : Digraph V) (w : V → ℝ≥0)
    (s v : V) (d : ℝ≥0) (h : vertexDistance G w s v ≠ ⊤) :
    (d ≤ 1 ∧ v ∈ levelCut G w s d) ↔
      d ∈ Set.Icc (vertexDistance G w s v).toNNReal
        (min 1 ((vertexDistance G w s v).toNNReal + w v)) := by
  rw [mem_levelCut_iff_of_distance_ne_top G w s v d h]
  simp only [Set.mem_Icc, le_min_iff]
  tauto

/-- Length of the vertex's threshold interval after clipping to `[0,1]`.
Truncated subtraction makes the length zero when its lower endpoint is above 1;
the separate infinite case makes unreachable vertices contribute zero. -/
def levelCutIntervalLength (G : Digraph V) (w : V → ℝ≥0) (s v : V) : ℝ≥0 :=
  if vertexDistance G w s v = ⊤ then 0 else
    min 1 ((vertexDistance G w s v).toNNReal + w v) -
      (vertexDistance G w s v).toNNReal

omit [Fintype V] in
/-- Deterministic individual-vertex interval bound underlying the marginal
probability estimate; no distribution or expectation is part of this claim. -/
theorem levelCutIntervalLength_le_weight (G : Digraph V) (w : V → ℝ≥0)
    (s v : V) : levelCutIntervalLength G w s v ≤ w v := by
  unfold levelCutIntervalLength
  split_ifs
  · exact zero_le
  · apply tsub_le_iff_right.mpr
    simpa only [add_comm] using
      (min_le_right 1 ((vertexDistance G w s v).toNNReal + w v))

end

end DirectedFlowCutGap
