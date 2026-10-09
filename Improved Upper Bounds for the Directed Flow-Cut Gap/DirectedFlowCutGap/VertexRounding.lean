import DirectedFlowCutGap.PathExtraction
import DirectedFlowCutGap.ZeroWeights

/-!
# Vertex rounding factors and finite weak decompositions

This is a graph-semantic bridge for the vertex case of Theorem 33 in
Bodwin–Samborska, arXiv:2604.03412v3 (`tex/reductions.tex`). A rounding
factor supplies actual integral cuts for the original graph's threshold
demands, for every nonnegative vertex cost. The corrected finite sampling
reduction then gives a uniform finite family of such cuts with marginal
at most `4 * α * w v`.

The factor property is an explicit hypothesis, not an assumed main bound.
Its domain is nonempty: the vertices with `1 ≤ card(V) * w v` give the
elementary `card(V)` factor. Zero weights, an empty vertex type, and a zero
factor are included. There is no claim here of an efficient sampler or of
the paper's stronger graph-theoretic approximation bounds.
-/

namespace DirectedFlowCutGap

noncomputable section

open scoped BigOperators NNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nonnegative rounding factor for the actual threshold demands of `G,w`.
Costs are finite nonnegative reals, including zero. -/
structure HasVertexRoundingFactor (G : Digraph V) (w : V → ℝ≥0) (α : ℝ) : Prop where
  nonneg : 0 ≤ α
  round : ∀ c : V → ℝ≥0, ∃ X : Finset V,
    IsIntegralCut G X (thresholdDemands G w) ∧
      (cutCost c X : ℝ) ≤ α * (weightedCost c w : ℝ)

omit [Fintype V] [DecidableEq V] in
/-- Explicit coercion of the integral objective to the real cost convention. -/
theorem coe_cutCost (c : V → ℝ≥0) (X : Finset V) :
    (cutCost c X : ℝ) = ∑ v ∈ X, (c v : ℝ) := by
  simp [cutCost]

omit [DecidableEq V] in
/-- Explicit coercion of the fractional objective to the MW convention. -/
theorem coe_weightedCost_eq_mwPotential (c w : V → ℝ≥0) :
    (weightedCost c w : ℝ) = mwPotential (fun v => (w v : ℝ))
      (fun v => (c v : ℝ)) := by
  simp [weightedCost, mwPotential]

/-- The graph rounding property provides exactly the real-valued cost oracle
required by finite sampling; the costs are converted using their given proofs
of nonnegativity. -/
theorem HasVertexRoundingFactor.real_cost_round
    {G : Digraph V} {w : V → ℝ≥0} {α : ℝ}
    (h : HasVertexRoundingFactor G w α)
    (c : V → ℝ) (hc : ∀ v, 0 ≤ c v) :
    ∃ X : Finset V, IsIntegralCut G X (thresholdDemands G w) ∧
      (∑ v ∈ X, c v) ≤ α * mwPotential (fun v => (w v : ℝ)) c := by
  let cNN : V → ℝ≥0 := fun v => NNReal.mk (c v) (hc v)
  obtain ⟨X, hX, hcost⟩ := h.round cNN
  refine ⟨X, hX, ?_⟩
  rw [coe_cutCost, coe_weightedCost_eq_mwPotential] at hcost
  simpa only [cNN, NNReal.coe_mk] using hcost

/-- A rounding factor yields a nonempty finite family of actual valid cuts.
The displayed quotient is the inclusion marginal under uniform sampling.
There is no positive-weight or positive-factor hypothesis. -/
theorem HasVertexRoundingFactor.exists_finite_vertex_weak_decomposition
    {G : Digraph V} {w : V → ℝ≥0} {α : ℝ}
    (h : HasVertexRoundingFactor G w α) :
    ∃ T : ℕ, 0 < T ∧ ∃ X : Fin T → Finset V,
      (∀ i, IsIntegralCut G (X i) (thresholdDemands G w)) ∧
      ∀ v, ((Finset.univ.filter fun i => v ∈ X i).card : ℝ) / (T : ℝ) ≤
        4 * α * (w v : ℝ) := by
  exact exists_finite_nonnegative_mw_family
    (fun v => (w v : ℝ)) α
    (fun X => IsIntegralCut G X (thresholdDemands G w))
    (fun v => (w v).coe_nonneg) h.nonneg h.real_cost_round

/-- The same family can be required to avoid every zero-weight vertex.
The explicit positive horizon also includes the empty graph and `α = 0`. -/
theorem HasVertexRoundingFactor.exists_vertex_weak_decomposition_avoiding_zero
    {G : Digraph V} {w : V → ℝ≥0} {α : ℝ}
    (h : HasVertexRoundingFactor G w α) :
    ∃ T : ℕ, 0 < T ∧ ∃ X : Fin T → Finset V,
      (∀ i, IsIntegralCut G (X i) (thresholdDemands G w)) ∧
      (∀ i v, v ∈ X i → 0 < w v) ∧
      ∀ v, ((Finset.univ.filter fun i => v ∈ X i).card : ℝ) / (T : ℝ) ≤
        4 * α * (w v : ℝ) := by
  obtain ⟨X, hX, hpos, hmarginal⟩ := exists_nonnegative_mw_family
    (fun v => (w v : ℝ)) α
    (fun X => IsIntegralCut G X (thresholdDemands G w))
    (fun v => (w v).coe_nonneg) h.nonneg h.real_cost_round
  refine ⟨mwNonnegativeHorizon (fun v => (w v : ℝ)) α,
    mwNonnegativeHorizon_pos _ _, X, hX, ?_, hmarginal⟩
  intro i v hv
  exact_mod_cast hpos i v hv

/-- With factor zero the empty cut is valid, and conversely. This includes
disconnected threshold pairs, for which there is no path to hit. -/
theorem hasVertexRoundingFactor_zero_iff (G : Digraph V) (w : V → ℝ≥0) :
    HasVertexRoundingFactor G w 0 ↔
      IsIntegralCut G ∅ (thresholdDemands G w) := by
  constructor
  · intro h
    exact mw_empty_admissible_of_zero (fun v => (w v : ℝ))
      (fun X => IsIntegralCut G X (thresholdDemands G w)) h.real_cost_round
  · intro h
    refine ⟨le_rfl, fun c => ⟨∅, h, ?_⟩⟩
    simp [cutCost]

omit [Fintype V] in
/-- Every surviving path in a valid threshold cut has original distance
strictly below one. Endpoints remain excluded from the cut condition. -/
theorem vertexDistance_lt_one_of_avoiding_threshold_cut
    {G : Digraph V} {w : V → ℝ≥0} {X : Finset V}
    (hX : IsIntegralCut G X (thresholdDemands G w))
    {s t : V} (p : SimplePath G s t) (hp : p.Avoids X) :
    vertexDistance G w s t < 1 := by
  by_contra h
  have hst : (s, t) ∈ thresholdDemands G w := le_of_not_gt h
  obtain ⟨v, hv, hvX⟩ := hX s t hst p
  exact hp v hv hvX

/-- A coarse deterministic threshold cut. No division by `card V` is used,
so this definition also applies to the empty graph. -/
def vertexCardThresholdCut (w : V → ℝ≥0) : Finset V :=
  Finset.univ.filter fun v => 1 ≤ (Fintype.card V : ℝ≥0) * w v

omit [DecidableEq V] in
@[simp] theorem mem_vertexCardThresholdCut (w : V → ℝ≥0) (v : V) :
    v ∈ vertexCardThresholdCut w ↔ 1 ≤ (Fintype.card V : ℝ≥0) * w v := by
  simp [vertexCardThresholdCut]

/-- Averaging over the actual internal vertex set: any simple path of weight
at least one has an internal vertex in the coarse threshold cut. -/
theorem SimplePath.meets_vertexCardThresholdCut
    {G : Digraph V} {s t : V} (p : SimplePath G s t)
    (w : V → ℝ≥0) (hp : 1 ≤ p.weight w) :
    ∃ v ∈ p.internalVertices, v ∈ vertexCardThresholdCut w := by
  by_contra h
  have hsmall : ∀ v ∈ p.internalVertices,
      (Fintype.card V : ℝ≥0) * w v < 1 := by
    intro v hv
    apply lt_of_not_ge
    intro hlarge
    exact h ⟨v, hv, (mem_vertexCardThresholdCut w v).mpr hlarge⟩
  have hne : p.internalVertices.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp [SimplePath.weight, he] at hp
  obtain ⟨v, hv⟩ := hne
  have hsum : (∑ u ∈ p.internalVertices,
      (Fintype.card V : ℝ≥0) * w u) <
      ∑ _u ∈ p.internalVertices, (1 : ℝ≥0) :=
    Finset.sum_lt_sum (fun u hu => (hsmall u hu).le) ⟨v, hv, hsmall v hv⟩
  have hstrict : (Fintype.card V : ℝ≥0) * p.weight w <
      (p.internalVertices.card : ℝ≥0) := by
    simpa [SimplePath.weight, Finset.mul_sum] using hsum
  have hcard : (p.internalVertices.card : ℝ≥0) ≤ (Fintype.card V : ℝ≥0) := by
    exact_mod_cast Finset.card_le_univ p.internalVertices
  have hlower : (Fintype.card V : ℝ≥0) ≤
      (Fintype.card V : ℝ≥0) * p.weight w := by
    simpa using mul_le_mul_of_nonneg_left hp
      (show (0 : ℝ≥0) ≤ Fintype.card V from zero_le)
  exact (not_lt_of_ge hlower) (hstrict.trans_le hcard)

/-- The coarse threshold set cuts every actual threshold demand. -/
theorem vertexCardThresholdCut_isIntegralCut (G : Digraph V) (w : V → ℝ≥0) :
    IsIntegralCut G (vertexCardThresholdCut w) (thresholdDemands G w) := by
  intro s t hst p
  have hp : 1 ≤ p.weight w :=
    (isFractionalCut_iff G w (thresholdDemands G w)).mp
      (isFractionalCut_thresholdDemands G w) s t hst p
  exact p.meets_vertexCardThresholdCut w hp

omit [DecidableEq V] in
/-- Charging each selected vertex to `card(V)` times its fractional cost. -/
theorem cutCost_vertexCardThresholdCut_le (c w : V → ℝ≥0) :
    cutCost c (vertexCardThresholdCut w) ≤
      (Fintype.card V : ℝ≥0) * weightedCost c w := by
  calc
    cutCost c (vertexCardThresholdCut w) ≤
        ∑ v ∈ vertexCardThresholdCut w,
          (Fintype.card V : ℝ≥0) * (c v * w v) := by
      apply Finset.sum_le_sum
      intro v hv
      have hlarge := (mem_vertexCardThresholdCut w v).mp hv
      calc
        c v = c v * 1 := (mul_one _).symm
        _ ≤ c v * ((Fintype.card V : ℝ≥0) * w v) :=
          mul_le_mul_of_nonneg_left hlarge zero_le
        _ = (Fintype.card V : ℝ≥0) * (c v * w v) := by ring
    _ ≤ ∑ v, (Fintype.card V : ℝ≥0) * (c v * w v) :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => zero_le)
    _ = (Fintype.card V : ℝ≥0) * weightedCost c w := by
      simp only [weightedCost, Finset.mul_sum]

/-- An unconditional, elementary graph rounding factor. -/
theorem hasVertexRoundingFactor_card (G : Digraph V) (w : V → ℝ≥0) :
    HasVertexRoundingFactor G w (Fintype.card V : ℝ) := by
  refine ⟨Nat.cast_nonneg _, fun c => ⟨vertexCardThresholdCut w,
    vertexCardThresholdCut_isIntegralCut G w, ?_⟩⟩
  have hcost := NNReal.coe_le_coe.mpr (cutCost_vertexCardThresholdCut_le c w)
  simpa only [NNReal.coe_mul, NNReal.coe_natCast] using hcost

/-- The factor domain is nonempty without postulating a graph oracle. -/
theorem exists_vertexRoundingFactor (G : Digraph V) (w : V → ℝ≥0) :
    ∃ α : ℝ, HasVertexRoundingFactor G w α :=
  ⟨Fintype.card V, hasVertexRoundingFactor_card G w⟩

end

end DirectedFlowCutGap
