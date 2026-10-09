import DirectedFlowCutGap.VertexFlow
import DirectedFlowCutGap.EdgeFlow

/-!
# Attained directed flow and cut optima

The paper's introductory flow-cut comparison (arXiv:2604.03412v3,
`intro.tex:55–60,206–241`) concerns maximum sum-multiflow, minimum fractional
multicut, and minimum integral multicut. The records below contain actual
witnesses and their quantified optimality proofs. They do not assume an optimum
value, duality, or an approximation inequality. Existence follows from the
proved flow dualities and minimization over a finite family of integral cuts.

Vertex cuts exclude both endpoints, so feasibility is required explicitly.
Edge feasibility likewise excludes diagonal demands. No value is assigned to
an infeasible instance. Empty, unreachable, and zero-capacity instances are
included, and optimal objective values are independent of the witnesses.
-/

namespace DirectedFlowCutGap

noncomputable section
open scoped BigOperators NNReal

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

namespace VertexOptima

variable {G : Digraph V} {D : Set (V × V)}

/-- Indicator of a vertex cut; endpoints are still excluded by path weights. -/
def indicator (X : Finset V) (v : V) : ℝ≥0 := if v ∈ X then 1 else 0

omit [Fintype V] in
/-- Every integral vertex cut is a feasible fractional cut with identical cost. -/
theorem indicator_isFractionalCut {X : Finset V} (hX : IsIntegralCut G X D) :
    IsFractionalCut G (indicator X) D := by
  rw [isFractionalCut_iff]
  intro s t hst p
  obtain ⟨v, hv, hx⟩ := hX s t hst p
  calc
    1 = indicator X v := by simp [indicator, hx]
    _ ≤ p.weight (indicator X) := Finset.single_le_sum (fun _ _ => zero_le) hv

/-- Exact identification of the integral and indicator fractional objectives. -/
theorem weightedCost_indicator (capacity : V → ℝ≥0) (X : Finset V) :
    weightedCost capacity (indicator X) = cutCost capacity X := by
  classical
  unfold weightedCost cutCost
  simp only [indicator, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  congr 1
  ext v
  simp

/-- The full vertex set is a cut whenever the fractional problem is feasible. -/
theorem univ_isIntegralCut {w₀ : V → ℝ≥0} (hw₀ : IsFractionalCut G w₀ D) :
    IsIntegralCut G Finset.univ D := by
  intro s t hst p
  obtain ⟨v, hv⟩ := VertexFlow.resources_nonempty_of_fractionalCut hw₀
    (⟨⟨(s, t), hst⟩, p⟩ : VertexFlow.PathIndex G D)
  exact ⟨v, hv, Finset.mem_univ v⟩

/-- Finite minimization proves actual integral optimum attainment. -/
theorem exists_minimum_integralCut (capacity : V → ℝ≥0) {w₀ : V → ℝ≥0}
    (hw₀ : IsFractionalCut G w₀ D) :
    ∃ X : Finset V, IsIntegralCut G X D ∧
      ∀ Y : Finset V, IsIntegralCut G Y D → cutCost capacity X ≤ cutCost capacity Y := by
  classical
  let C := {X : Finset V // IsIntegralCut G X D}
  have : Nonempty C := ⟨⟨Finset.univ, univ_isIntegralCut hw₀⟩⟩
  obtain ⟨X, hX⟩ := Finite.exists_min (fun X : C => cutCost capacity X.val)
  exact ⟨X.val, X.property, fun Y hY => hX ⟨Y, hY⟩⟩

/-- Actual attained optimizers, not supplied numerical optimum values. -/
structure Solution (G : Digraph V) (D : Set (V × V)) (capacity : V → ℝ≥0) where
  flow : VertexFlow.Flow G D
  weight : V → ℝ≥0
  cut : Finset V
  flow_feasible : VertexFlow.IsFeasible capacity flow
  fractional_feasible : IsFractionalCut G weight D
  integral_feasible : IsIntegralCut G cut D
  flow_maximal : ∀ f : VertexFlow.Flow G D, VertexFlow.IsFeasible capacity f →
    VertexFlow.value f ≤ VertexFlow.value flow
  fractional_minimal : ∀ w : V → ℝ≥0, IsFractionalCut G w D →
    weightedCost capacity weight ≤ weightedCost capacity w
  integral_minimal : ∀ X : Finset V, IsIntegralCut G X D →
    cutCost capacity cut ≤ cutCost capacity X
  objectives_eq : VertexFlow.value flow = weightedCost capacity weight
  weights_le_one : ∀ v, weight v ≤ 1

/-- All three optimum witnesses exist from an arbitrary feasible fractional cut. -/
theorem exists_solution (capacity w₀ : V → ℝ≥0) (hw₀ : IsFractionalCut G w₀ D) :
    Nonempty (Solution G D capacity) := by
  obtain ⟨f, w, hf, hw, heq, hmax, hmin, hw1⟩ := VertexFlow.strong_duality capacity w₀ hw₀
  obtain ⟨X, hX, hXmin⟩ := exists_minimum_integralCut capacity hw₀
  exact ⟨⟨f, w, X, hf, hw, hX, hmax, hmin, hXmin, heq, hw1⟩⟩

/-- Exact domain of the attained vertex problems: every demanded path has an
internal resource. In particular, infeasible endpoint-only paths are excluded. -/
theorem exists_solution_iff_nonempty_resources (capacity : V → ℝ≥0) :
    Nonempty (Solution G D capacity) ↔
      ∀ p : VertexFlow.PathIndex G D, (VertexFlow.resources p).Nonempty := by
  constructor
  · rintro ⟨S⟩
    exact VertexFlow.resources_nonempty_of_fractionalCut S.fractional_feasible
  · intro h
    obtain ⟨w, hw⟩ := VertexFlow.exists_fractionalCut_iff.mpr h
    exact exists_solution capacity w hw

/-- A directly adjacent demand admits no attained solution in the vertex model. -/
theorem no_solution_of_adj (capacity : V → ℝ≥0) {s t : V}
    (hst : (s, t) ∈ D) (hadj : G.Adj s t) : ¬ Nonempty (Solution G D capacity) := by
  rintro ⟨S⟩
  exact VertexFlow.no_fractionalCut_of_adj hst hadj ⟨S.weight, S.fractional_feasible⟩

/-- Diagonal vertex demands likewise lie outside the finite optimum domain. -/
theorem no_solution_of_self (capacity : V → ℝ≥0) {s : V} (hs : (s, s) ∈ D) :
    ¬ Nonempty (Solution G D capacity) := by
  rintro ⟨S⟩
  exact VertexFlow.no_fractionalCut_of_self hs ⟨S.weight, S.fractional_feasible⟩

variable {capacity : V → ℝ≥0}

/-- Maximum flow cannot exceed the attained integral minimum. -/
theorem flow_le_integral (S : Solution G D capacity) :
    VertexFlow.value S.flow ≤ cutCost capacity S.cut := by
  have h := VertexFlow.weak_duality S.flow_feasible
    (indicator_isFractionalCut S.integral_feasible)
  rwa [weightedCost_indicator] at h

/-- Every optimizer choice has the same integral, fractional, and flow values. -/
theorem objective_values_unique (S T : Solution G D capacity) :
    cutCost capacity S.cut = cutCost capacity T.cut ∧
    weightedCost capacity S.weight = weightedCost capacity T.weight ∧
    VertexFlow.value S.flow = VertexFlow.value T.flow := by
  exact ⟨le_antisymm (S.integral_minimal _ T.integral_feasible)
      (T.integral_minimal _ S.integral_feasible),
    le_antisymm (S.fractional_minimal _ T.fractional_feasible)
      (T.fractional_minimal _ S.fractional_feasible),
    le_antisymm (T.flow_maximal _ S.flow_feasible)
      (S.flow_maximal _ T.flow_feasible)⟩

/-- Unreachable demands have all three optimum values zero. -/
theorem objectives_eq_zero_of_unreachable (S : Solution G D capacity)
    (h : ∀ s t, (s, t) ∈ D → ¬ Nonempty (SimplePath G s t)) :
    VertexFlow.value S.flow = 0 ∧ weightedCost capacity S.weight = 0 ∧
      cutCost capacity S.cut = 0 := by
  have hf := VertexFlow.value_eq_zero_of_unreachable h S.flow
  refine ⟨hf, S.objectives_eq.symm.trans hf, le_antisymm ?_ zero_le⟩
  have he : IsIntegralCut G ∅ D := fun s t hst p => (h s t hst ⟨p⟩).elim
  simpa [cutCost] using S.integral_minimal ∅ he

/-- Empty demands are included without a positive optimum assumption. -/
theorem objectives_eq_zero_empty (S : Solution G ∅ capacity) :
    VertexFlow.value S.flow = 0 ∧ weightedCost capacity S.weight = 0 ∧
      cutCost capacity S.cut = 0 :=
  objectives_eq_zero_of_unreachable S (fun _ _ h => h.elim)

end VertexOptima

namespace EdgeOptima

variable {G : Digraph V} {D : Set (V × V)}

/-- All actual edges cut every feasible demand, including adjacent demands. -/
theorem graphEdges_isIntegralCut {w₀ : V × V → ℝ≥0}
    (hw₀ : IsFractionalEdgeCut G w₀ D) : IsIntegralEdgeCut G (graphEdges G) D := by
  intro s t hst p
  obtain ⟨e, he⟩ := EdgeFlow.resources_nonempty_of_fractionalCut hw₀
    (⟨⟨(s, t), hst⟩, p⟩ : EdgeFlow.PathIndex G D)
  exact ⟨e, he, p.edges_subset_graphEdges he⟩

/-- The attained minimum selects only actual edges and minimizes over all cuts.
Allowing nonedges in the comparison does not change its objective. -/
theorem exists_minimum_integralCut (capacity : V × V → ℝ≥0) {w₀ : V × V → ℝ≥0}
    (hw₀ : IsFractionalEdgeCut G w₀ D) :
    ∃ X : Finset (V × V), X ⊆ graphEdges G ∧ IsIntegralEdgeCut G X D ∧
      ∀ Y : Finset (V × V), IsIntegralEdgeCut G Y D →
        edgeCutCost G capacity X ≤ edgeCutCost G capacity Y := by
  classical
  let C := {X : Finset (V × V) // IsIntegralEdgeCut G X D}
  have : Nonempty C := ⟨⟨graphEdges G, graphEdges_isIntegralCut hw₀⟩⟩
  obtain ⟨X, hX⟩ := Finite.exists_min (fun X : C => edgeCutCost G capacity X.val)
  refine ⟨X.val.filter (fun e => G.Adj e.1 e.2), ?_, ?_, ?_⟩
  · intro e he
    exact (mem_graphEdges G e).mpr (Finset.mem_filter.mp he).2
  · intro s t hst
    exact (edgeCutsPair_filter_actual G X.val s t).mpr (X.property s t hst)
  · intro Y hY
    rw [edgeCutCost_filter_actual]
    exact hX ⟨Y, hY⟩

/-- All objectives and feasibility predicates use actual edge resources. -/
structure Solution (G : Digraph V) (D : Set (V × V)) (capacity : V × V → ℝ≥0) where
  flow : EdgeFlow.Flow G D
  weight : V × V → ℝ≥0
  cut : Finset (V × V)
  cut_edges : cut ⊆ graphEdges G
  flow_feasible : EdgeFlow.IsFeasible capacity flow
  fractional_feasible : IsFractionalEdgeCut G weight D
  integral_feasible : IsIntegralEdgeCut G cut D
  flow_maximal : ∀ f : EdgeFlow.Flow G D, EdgeFlow.IsFeasible capacity f →
    EdgeFlow.value f ≤ EdgeFlow.value flow
  fractional_minimal : ∀ w : V × V → ℝ≥0, IsFractionalEdgeCut G w D →
    weightedEdgeCost G capacity weight ≤ weightedEdgeCost G capacity w
  integral_minimal : ∀ X : Finset (V × V), IsIntegralEdgeCut G X D →
    edgeCutCost G capacity cut ≤ edgeCutCost G capacity X
  objectives_eq : EdgeFlow.value flow = weightedEdgeCost G capacity weight
  weights_le_one : ∀ e, weight e ≤ 1

/-- Attainment and duality require only a feasible fractional input witness. -/
theorem exists_solution (capacity w₀ : V × V → ℝ≥0)
    (hw₀ : IsFractionalEdgeCut G w₀ D) : Nonempty (Solution G D capacity) := by
  obtain ⟨f, w, hf, hw, heq, hmax, hmin, hw1⟩ := EdgeFlow.strong_duality capacity w₀ hw₀
  obtain ⟨X, hXe, hX, hXmin⟩ := exists_minimum_integralCut capacity hw₀
  exact ⟨⟨f, w, X, hXe, hf, hw, hX, hmax, hmin, hXmin, heq, hw1⟩⟩

/-- The exact edge feasibility domain is the absence of diagonal demands. -/
theorem exists_solution_iff_no_self (capacity : V × V → ℝ≥0) :
    Nonempty (Solution G D capacity) ↔ ∀ s, (s, s) ∉ D := by
  constructor
  · rintro ⟨S⟩
    exact EdgeFlow.exists_fractionalCut_iff_no_self.mp ⟨S.weight, S.fractional_feasible⟩
  · intro h
    obtain ⟨w, hw⟩ := EdgeFlow.exists_fractionalCut_iff_no_self.mpr h
    exact exists_solution capacity w hw

variable {capacity : V × V → ℝ≥0}

/-- Weak duality compares maximum flow with the attained integral optimum. -/
theorem flow_le_integral (S : Solution G D capacity) :
    EdgeFlow.value S.flow ≤ edgeCutCost G capacity S.cut := by
  have h := EdgeFlow.weak_duality S.flow_feasible
    ((isIntegralEdgeCut_iff_indicator G S.cut D).mp S.integral_feasible)
  rwa [weightedEdgeCost_indicator] at h

/-- The three optimum objectives are independent of every choice of witness. -/
theorem objective_values_unique (S T : Solution G D capacity) :
    edgeCutCost G capacity S.cut = edgeCutCost G capacity T.cut ∧
    weightedEdgeCost G capacity S.weight = weightedEdgeCost G capacity T.weight ∧
    EdgeFlow.value S.flow = EdgeFlow.value T.flow := by
  exact ⟨le_antisymm (S.integral_minimal _ T.integral_feasible)
      (T.integral_minimal _ S.integral_feasible),
    le_antisymm (S.fractional_minimal _ T.fractional_feasible)
      (T.fractional_minimal _ S.fractional_feasible),
    le_antisymm (T.flow_maximal _ S.flow_feasible)
      (S.flow_maximal _ T.flow_feasible)⟩

/-- Unreachable demand families have all three optimum values zero. -/
theorem objectives_eq_zero_of_unreachable (S : Solution G D capacity)
    (h : ∀ s t, (s, t) ∈ D → ¬ Nonempty (SimplePath G s t)) :
    EdgeFlow.value S.flow = 0 ∧ weightedEdgeCost G capacity S.weight = 0 ∧
      edgeCutCost G capacity S.cut = 0 := by
  have hf := EdgeFlow.value_eq_zero_of_unreachable h S.flow
  refine ⟨hf, S.objectives_eq.symm.trans hf, le_antisymm ?_ zero_le⟩
  have he : IsIntegralEdgeCut G ∅ D := fun s t hst p => (h s t hst ⟨p⟩).elim
  simpa [edgeCutCost] using S.integral_minimal ∅ he

/-- The empty demand case follows with no nonempty-graph assumption. -/
theorem objectives_eq_zero_empty (S : Solution G ∅ capacity) :
    EdgeFlow.value S.flow = 0 ∧ weightedEdgeCost G capacity S.weight = 0 ∧
      edgeCutCost G capacity S.cut = 0 :=
  objectives_eq_zero_of_unreachable S (fun _ _ h => h.elim)

end EdgeOptima
end
end DirectedFlowCutGap
