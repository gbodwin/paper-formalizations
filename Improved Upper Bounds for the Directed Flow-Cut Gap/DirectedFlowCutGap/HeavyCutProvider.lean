import DirectedFlowCutGap.StatefulHeavyValidity
import DirectedFlowCutGap.StatefulHeavyRate
import DirectedFlowCutGap.BinaryZeroAvoidingProbability

/-! A proof-indexed adapter from the same actual heavy query to the binary
packing provider interface. It supplies the original fixed weights and exact
current binary cost row after raw decoding, and retains the returned mask,
operations and physical sampler metadata. The support index adds only an erased
validity certificate; it does not filter outcomes or retry a query.

This closes the pointwise quality contract, uniformly over the cost row. The
raw decoder's materialization charge, adaptive-controller composition, and
physical storage/runtime are still separate. Each PMF provider call has its
specified local entering ledger; it is not a claimed shared-ledger controller. -/
namespace DirectedFlowCutGap.HeavyCutProvider
noncomputable section
open scoped BigOperators ENNReal NNReal
open BinaryFractionalRows BinarySamplerMetadata BinaryZeroAvoidingProvider
open BinaryZeroAvoidingSelector BinaryZeroAvoidingProbability
open EncodedUnitCostReplication
set_option backward.isDefEq.respectTransparency false

/-- Explicit raw-array boundary; its binary materialization cost is not
included in the returned query operation field. -/
def input {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w c : Row n) : Input n :=
  ⟨adjacency,decodeRow w,decodeRow c⟩

def columns {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) :
    Set (FractionalCover.Column n) :=
  {X | IsIntegralCut (input adjacency w w).graph X
    (thresholdDemands (input adjacency w w).graph (input adjacency w w).weight)}

theorem input_weight {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w c : Row n) (i : Fin n) :
    ((input adjacency w c).weight i : ℝ)=tableValue w i := by
  simp [input,Input.weight,decodeRow,BinaryFractionalRows.get,tableValue_apply,
    RawNonnegativeRational.Code.realValue]

theorem input_cost {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w c : Row n) (i : Fin n) :
    ((input adjacency w c).cost i : ℝ)=tableValue c i := by
  simp [input,Input.cost,decodeRow,BinaryFractionalRows.get,tableValue_apply,
    RawNonnegativeRational.Code.realValue]

theorem objective_eq {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w c : Row n) :
    (weightedCost (input adjacency w c).cost (input adjacency w c).weight : ℝ)=
      ZeroAvoidingSelector.mwPotential (tableValue w) (tableValue c) := by
  simp only [weightedCost,ZeroAvoidingSelector.mwPotential,NNReal.coe_sum,NNReal.coe_mul,
    input_weight,input_cost]

theorem cut_cost_eq {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w c : Row n)
    (mask : Vector Bool n) :
    (cutCost (input adjacency w c).cost (EncodedUnitCostReplication.selectedSet mask) : ℝ)=
      ∑ i∈column mask, tableValue c i := by
  simp only [cutCost,NNReal.coe_sum,input_cost]
  rfl

def answer {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w c : Row n)
    (extra : ℕ) (state : Ledger) (out : EncodedWeightedVertexQuery.Output n × Ledger)
    (ho : out∈((StatefulHeavyQuery.run (input adjacency w c) extra).run state).support) :
    CutAnswer (columns adjacency w) where
  mask := some out.1.mask
  operations := out.1.operations+8
  failed := out.2.failed
  trials := out.2.trials
  consumed := out.2.consumed
  valid := by
    intro x hx
    have he : out.1.mask=x := Option.some.inj hx
    subst x
    exact StatefulHeavyValidity.heavy_valid (input adjacency w c) extra state ho

/-- Exactly one original query, with proof-only support indexing. -/
def draw {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n)
    (extra : ℕ) (state : Ledger) : CutProvider PMF (columns adjacency w) := fun c =>
  ((StatefulHeavyQuery.run (input adjacency w c) extra).run state).bindOnSupport
    (fun out ho => PMF.pure (answer adjacency w c extra state out ho))

private theorem support_push_failure {A B : Type} (μ : PMF A)
    (f : ∀ a∈μ.support, B) (E : Set B) (F : Set A)
    (h : ∀ a ha, f a ha∈E → a∈F) :
    (μ.bindOnSupport (fun a ha => PMF.pure (f a ha))).toOuterMeasure E ≤
      μ.toOuterMeasure F := by
  classical
  rw [PMF.toOuterMeasure_bindOnSupport_apply,PMF.toOuterMeasure_apply]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : μ a=0
  · simp [ha]
  · rw [dite_eq_right ha,PMF.toOuterMeasure_pure_apply]
    by_cases he : f a ha∈E
    · have hf := h a ha he
      simp [he,hf]
    · simp [he]

/-- One graph-size constant precedes the original graph/weights, every current
cost row, confidence parameter and entering ledger. No caller quality law is
assumed. The event uses the exact current row in the original provider interface. -/
theorem uniform_query_failure :
    ∀ δ : ℝ, 0<δ → ∃ K : ℝ, 0<K ∧
      ∀ (n : ℕ) (_hn : 0<n) (adjacency : RetainedGridState.PairFlags n)
        (w c : Row n) (k : ℕ) (state : Ledger),
      (draw adjacency w (3*k) state c).toOuterMeasure
        (queryFailure w c (K*(n:ℝ)^((1:ℝ)/3+δ))) ≤ ENNReal.ofReal (((1:ℝ)/2)^k) := by
  intro δ hδ
  obtain ⟨K,hK,hquality⟩ := StatefulHeavyRate.uniform_confidence δ hδ
  refine ⟨K,hK,?_⟩
  intro n hn adjacency w c k state
  let D := input adjacency w c
  let μ := (StatefulHeavyQuery.run D (3*k)).run state
  have hpush := support_push_failure μ (answer adjacency w c (3*k) state)
    (queryFailure w c (K*(n:ℝ)^((1:ℝ)/3+δ)))
    {out | ¬StatefulHeavyRate.Good D K δ (3*k) state out} (by
      intro out ho hbad hgood
      have hc := hgood.2.1
      change (cutCost (input adjacency w c).cost
        (EncodedUnitCostReplication.selectedSet out.1.mask) : ℝ) ≤ _ at hc
      rw [cut_cost_eq,objective_eq] at hc
      exact (not_lt_of_ge hc) hbad)
  have hq := hquality n hn D k state
  have hfinite : μ.toOuterMeasure {out | ¬StatefulHeavyRate.Good D K δ (3*k) state out} ≠ ⊤ := by
    rw [PMF.toOuterMeasure_apply]
    exact μ.tsum_coe_indicator_ne_top _
  exact hpush.trans ((ENNReal.ofReal_toReal hfinite).symm.le.trans (ENNReal.ofReal_le_ofReal hq))

/-- The charged event is a subset of this same actual penalized query's cost
failure, so the contract needed by the existing zero-avoiding adapter follows. -/
theorem uniform_charged_failure :
    ∀ δ : ℝ, 0<δ → ∃ K : ℝ, 0<K ∧
      ∀ (n : ℕ) (_hn : 0<n) (adjacency : RetainedGridState.PairFlags n)
        (w c : Row n) (k : ℕ) (state : Ledger),
      (draw adjacency w (3*k) state (BinaryZeroAvoidingSelector.prepare w c).costs).toOuterMeasure
        (chargedFailure w c (K*(n:ℝ)^((1:ℝ)/3+δ))) ≤ ENNReal.ofReal (((1:ℝ)/2)^k) := by
  intro δ hδ
  obtain ⟨K,hK,hq⟩ := uniform_query_failure δ hδ
  refine ⟨K,hK,?_⟩
  intro n hn adjacency w c k state
  exact ((draw adjacency w (3*k) state (BinaryZeroAvoidingSelector.prepare w c).costs).toOuterMeasure.mono
    (chargedFailure_subset w c _ (columns adjacency w))).trans
    (hq n hn adjacency w (BinaryZeroAvoidingSelector.prepare w c).costs k state)

end
end DirectedFlowCutGap.HeavyCutProvider
