import DirectedFlowCutGap.AttainedOptima
import DirectedFlowCutGap.AdaptiveVertexBound
import DirectedFlowCutGap.AdaptiveEdgeBound

/-!
# Main flow-cut inequalities with genuine attained optima

This is the optimization interpretation of Theorems 1 and 2 in
arXiv:2604.03412v3, `intro.tex:222–241`, and the cost inequalities stated in
`body.tex:17–43`. For every positive epsilon there is one positive constant,
chosen before all graph instances, such that the attained minimum integral cut
is bounded both by K n^(1/3+epsilon) times the attained maximum sum-multiflow and
by K n^epsilon sqrt(W) times that same optimum. W is explicitly the total weight
of the selected attained minimum fractional cut. The duality equality also
makes these inequalities statements against the minimum fractional objective.

Feasible fractional witnesses are the only domain assumptions in the final
existence theorem. Infeasible vertex demands and diagonal edge demands are not
silently assigned optimum values. The theorem includes empty graphs, empty or
unreachable demand families, and zero capacities or objective values. We use
cost inequalities, without dividing by a possibly zero optimum. The final
zero-objective lemmas prove that zero maximum flow forces zero integral cost.
No claim about algorithmic implementation or running time is made here.
-/

namespace DirectedFlowCutGap.OptimalFlowCutBounds

noncomputable section
open scoped NNReal
universe u

/-- The size bound for every choice of attained vertex optima. -/
theorem vertex_size_bound_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0, 0 < K ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V)
        (D : Set (V × V)) (capacity : V → ℝ≥0) (S : VertexOptima.Solution G D capacity),
        cutCost capacity S.cut ≤
          (K * (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε)) * VertexFlow.value S.flow := by
  intro ε hε
  obtain ⟨K, hK, hround⟩ := AdaptiveVertexBound.vertex_rounding_uniform.{u} ε hε
  refine ⟨K, hK, ?_⟩
  intro V _ _ G D capacity S
  obtain ⟨X, hX, hx⟩ := hround V G S.weight capacity
  have hXD : IsIntegralCut G X D := fun s t hst => hX s t (S.fractional_feasible s t hst)
  calc
    cutCost capacity S.cut ≤ cutCost capacity X := S.integral_minimal X hXD
    _ ≤ (K * (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε)) *
        weightedCost capacity S.weight := hx
    _ = _ := by rw [S.objectives_eq]

/-- Here W is the total weight of the selected minimum fractional vertex cut. -/
theorem vertex_weight_bound_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0, 0 < K ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V)
        (D : Set (V × V)) (capacity : V → ℝ≥0) (S : VertexOptima.Solution G D capacity),
        cutCost capacity S.cut ≤ (K * (Fintype.card V : ℝ≥0) ^ ε *
          totalWeight S.weight ^ (1 / 2 : ℝ)) * VertexFlow.value S.flow := by
  intro ε hε
  obtain ⟨K, hK, hround⟩ := AdaptiveVertexBound.vertex_weight_rounding_uniform.{u} ε hε
  refine ⟨K, hK, ?_⟩
  intro V _ _ G D capacity S
  obtain ⟨X, hX, hx⟩ := hround V G S.weight capacity
  have hXD : IsIntegralCut G X D := fun s t hst => hX s t (S.fractional_feasible s t hst)
  calc
    cutCost capacity S.cut ≤ cutCost capacity X := S.integral_minimal X hXD
    _ ≤ (K * (Fintype.card V : ℝ≥0) ^ ε * totalWeight S.weight ^ (1 / 2 : ℝ)) *
        weightedCost capacity S.weight := hx
    _ = _ := by rw [S.objectives_eq]

/-- The size bound for actual minimum edge cut and maximum edge sum-multiflow. -/
theorem edge_size_bound_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0, 0 < K ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V)
        (D : Set (V × V)) (capacity : V × V → ℝ≥0) (S : EdgeOptima.Solution G D capacity),
        edgeCutCost G capacity S.cut ≤
          (K * (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε)) * EdgeFlow.value S.flow := by
  intro ε hε
  obtain ⟨K, hK, hround⟩ := AdaptiveEdgeBound.edge_rounding_uniform.{u} ε hε
  refine ⟨K, hK, ?_⟩
  intro V _ _ G D capacity S
  obtain ⟨X, _, hX, hx⟩ := hround V G S.weight capacity
  have hXD : IsIntegralEdgeCut G X D := fun s t hst => hX s t (S.fractional_feasible s t hst)
  calc
    edgeCutCost G capacity S.cut ≤ edgeCutCost G capacity X := S.integral_minimal X hXD
    _ ≤ (K * (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε)) *
        weightedEdgeCost G capacity S.weight := hx
    _ = _ := by rw [S.objectives_eq]

/-- W sums only actual edge weights of the selected minimum fractional cut. -/
theorem edge_weight_bound_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0, 0 < K ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V)
        (D : Set (V × V)) (capacity : V × V → ℝ≥0) (S : EdgeOptima.Solution G D capacity),
        edgeCutCost G capacity S.cut ≤ (K * (Fintype.card V : ℝ≥0) ^ ε *
          totalEdgeWeight G S.weight ^ (1 / 2 : ℝ)) * EdgeFlow.value S.flow := by
  intro ε hε
  obtain ⟨K, hK, hround⟩ := AdaptiveEdgeBound.edge_weight_rounding_uniform.{u} ε hε
  refine ⟨K, hK, ?_⟩
  intro V _ _ G D capacity S
  obtain ⟨X, _, hX, hx⟩ := hround V G S.weight capacity
  have hXD : IsIntegralEdgeCut G X D := fun s t hst => hX s t (S.fractional_feasible s t hst)
  calc
    edgeCutCost G capacity S.cut ≤ edgeCutCost G capacity X := S.integral_minimal X hXD
    _ ≤ (K * (Fintype.card V : ℝ≥0) ^ ε * totalEdgeWeight G S.weight ^ (1 / 2 : ℝ)) *
        weightedEdgeCost G capacity S.weight := hx
    _ = _ := by rw [S.objectives_eq]

/-- Both main inequalities for the same attained vertex integral optimum. -/
def VertexBounds (ε : ℝ) (K : ℝ≥0) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V)
    (D : Set (V × V)) (capacity : V → ℝ≥0) (S : VertexOptima.Solution G D capacity),
    cutCost capacity S.cut ≤
      (K * (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε)) * VertexFlow.value S.flow ∧
    cutCost capacity S.cut ≤ (K * (Fintype.card V : ℝ≥0) ^ ε *
      totalWeight S.weight ^ (1 / 2 : ℝ)) * VertexFlow.value S.flow

/-- Both main inequalities for the same attained edge integral optimum. -/
def EdgeBounds (ε : ℝ) (K : ℝ≥0) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V)
    (D : Set (V × V)) (capacity : V × V → ℝ≥0) (S : EdgeOptima.Solution G D capacity),
    edgeCutCost G capacity S.cut ≤
      (K * (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε)) * EdgeFlow.value S.flow ∧
    edgeCutCost G capacity S.cut ≤ (K * (Fintype.card V : ℝ≥0) ^ ε *
      totalEdgeWeight G S.weight ^ (1 / 2 : ℝ)) * EdgeFlow.value S.flow

/-- One constant works simultaneously for both main bounds in both models.
It depends on epsilon, not on size, graph, capacities, demands, or optimizers. -/
theorem main_bounds_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0, 0 < K ∧ VertexBounds.{u} ε K ∧ EdgeBounds.{u} ε K := by
  intro ε hε
  obtain ⟨Kv, hKv, hv⟩ := vertex_size_bound_uniform.{u} ε hε
  obtain ⟨Kw, _, hw⟩ := vertex_weight_bound_uniform.{u} ε hε
  obtain ⟨Ke, _, he⟩ := edge_size_bound_uniform.{u} ε hε
  obtain ⟨Kf, _, hf⟩ := edge_weight_bound_uniform.{u} ε hε
  let K := max (max Kv Kw) (max Ke Kf)
  have hKvK : Kv ≤ K := (le_max_left Kv Kw).trans (le_max_left _ _)
  have hKwK : Kw ≤ K := (le_max_right Kv Kw).trans (le_max_left _ _)
  have hKeK : Ke ≤ K := (le_max_left Ke Kf).trans (le_max_right _ _)
  have hKfK : Kf ≤ K := (le_max_right Ke Kf).trans (le_max_right _ _)
  refine ⟨K, hKv.trans_le hKvK, ?_, ?_⟩
  · intro V _ _ G D capacity S
    constructor
    · exact (hv V G D capacity S).trans (by gcongr)
    · exact (hw V G D capacity S).trans (by gcongr)
  · intro V _ _ G D capacity S
    constructor
    · exact (he V G D capacity S).trans (by gcongr)
    · exact (hf V G D capacity S).trans (by gcongr)

/-- The mathematical forms of Theorems 1 and 2 with all optima attained.
Only feasible input weights are supplied; maximum flow, minimum fractional cut,
and minimum integral cut witnesses are all constructed by proved theorems. -/
theorem main_theorems_attained_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0, 0 < K ∧
      (∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V)
        (D : Set (V × V)) (capacity w₀ : V → ℝ≥0), IsFractionalCut G w₀ D →
        ∃ S : VertexOptima.Solution G D capacity,
          cutCost capacity S.cut ≤
            (K * (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε)) * VertexFlow.value S.flow ∧
          cutCost capacity S.cut ≤ (K * (Fintype.card V : ℝ≥0) ^ ε *
            totalWeight S.weight ^ (1 / 2 : ℝ)) * VertexFlow.value S.flow) ∧
      (∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V)
        (D : Set (V × V)) (capacity w₀ : V × V → ℝ≥0), IsFractionalEdgeCut G w₀ D →
        ∃ S : EdgeOptima.Solution G D capacity,
          edgeCutCost G capacity S.cut ≤
            (K * (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε)) * EdgeFlow.value S.flow ∧
          edgeCutCost G capacity S.cut ≤ (K * (Fintype.card V : ℝ≥0) ^ ε *
            totalEdgeWeight G S.weight ^ (1 / 2 : ℝ)) * EdgeFlow.value S.flow) := by
  intro ε hε
  obtain ⟨K, hK, hv, he⟩ := main_bounds_uniform.{u} ε hε
  refine ⟨K, hK, ?_, ?_⟩
  · intro V _ _ G D capacity w₀ hw₀
    obtain ⟨S⟩ := VertexOptima.exists_solution capacity w₀ hw₀
    exact ⟨S, hv V G D capacity S⟩
  · intro V _ _ G D capacity w₀ hw₀
    obtain ⟨S⟩ := EdgeOptima.exists_solution capacity w₀ hw₀
    exact ⟨S, he V G D capacity S⟩

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : Digraph V} {D : Set (V × V)}

/-- The same two vertex inequalities against the minimum fractional objective. -/
theorem vertex_bounds_against_fractional {ε : ℝ} {K : ℝ≥0}
    (h : VertexBounds.{u} ε K) {capacity : V → ℝ≥0}
    (S : VertexOptima.Solution G D capacity) :
    cutCost capacity S.cut ≤
      (K * (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε)) * weightedCost capacity S.weight ∧
    cutCost capacity S.cut ≤ (K * (Fintype.card V : ℝ≥0) ^ ε *
      totalWeight S.weight ^ (1 / 2 : ℝ)) * weightedCost capacity S.weight := by
  simpa only [S.objectives_eq] using h V G D capacity S

/-- The same two edge inequalities against the minimum fractional objective. -/
theorem edge_bounds_against_fractional {ε : ℝ} {K : ℝ≥0}
    (h : EdgeBounds.{u} ε K) {capacity : V × V → ℝ≥0}
    (S : EdgeOptima.Solution G D capacity) :
    edgeCutCost G capacity S.cut ≤
      (K * (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε)) * weightedEdgeCost G capacity S.weight ∧
    edgeCutCost G capacity S.cut ≤ (K * (Fintype.card V : ℝ≥0) ^ ε *
      totalEdgeWeight G S.weight ^ (1 / 2 : ℝ)) * weightedEdgeCost G capacity S.weight := by
  simpa only [S.objectives_eq] using h V G D capacity S

/-- Zero maximum vertex flow entails zero integral optimum; no quotient is used. -/
theorem vertex_integral_eq_zero_of_flow_eq_zero {capacity : V → ℝ≥0}
    (S : VertexOptima.Solution G D capacity) (h : VertexFlow.value S.flow = 0) :
    cutCost capacity S.cut = 0 := by
  obtain ⟨K, _, hK⟩ := vertex_size_bound_uniform.{u} 1 (by norm_num)
  have hx := hK V G D capacity S
  rw [h, mul_zero] at hx
  exact le_antisymm hx zero_le

/-- Zero maximum edge flow likewise entails zero integral optimum. -/
theorem edge_integral_eq_zero_of_flow_eq_zero {capacity : V × V → ℝ≥0}
    (S : EdgeOptima.Solution G D capacity) (h : EdgeFlow.value S.flow = 0) :
    edgeCutCost G capacity S.cut = 0 := by
  obtain ⟨K, _, hK⟩ := edge_size_bound_uniform.{u} 1 (by norm_num)
  have hx := hK V G D capacity S
  rw [h, mul_zero] at hx
  exact le_antisymm hx zero_le

/-- The zero-objective cases agree in the vertex model, with no 0/0 convention. -/
theorem vertex_integral_eq_zero_iff_fractional_eq_zero {capacity : V → ℝ≥0}
    (S : VertexOptima.Solution G D capacity) :
    cutCost capacity S.cut = 0 ↔ weightedCost capacity S.weight = 0 := by
  constructor
  · intro h
    have hf : VertexFlow.value S.flow = 0 := le_antisymm (by
      simpa only [h] using VertexOptima.flow_le_integral S) zero_le
    exact S.objectives_eq.symm.trans hf
  · intro h
    exact vertex_integral_eq_zero_of_flow_eq_zero S (S.objectives_eq.trans h)

/-- The edge model has the same exact zero-objective equivalence. -/
theorem edge_integral_eq_zero_iff_fractional_eq_zero {capacity : V × V → ℝ≥0}
    (S : EdgeOptima.Solution G D capacity) :
    edgeCutCost G capacity S.cut = 0 ↔ weightedEdgeCost G capacity S.weight = 0 := by
  constructor
  · intro h
    have hf : EdgeFlow.value S.flow = 0 := le_antisymm (by
      simpa only [h] using EdgeOptima.flow_le_integral S) zero_le
    exact S.objectives_eq.symm.trans hf
  · intro h
    exact edge_integral_eq_zero_of_flow_eq_zero S (S.objectives_eq.trans h)

end
end DirectedFlowCutGap.OptimalFlowCutBounds
