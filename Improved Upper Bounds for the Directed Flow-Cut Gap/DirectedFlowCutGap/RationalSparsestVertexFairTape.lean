import DirectedFlowCutGap.RationalSparsestVertexExpectation

/-! A finite fair-tape upper-tail bound for either endpoint-safe vertex mode. -/
namespace DirectedFlowCutGap.RationalSparsestVertexFairTape

noncomputable section
open scoped NNReal NNRat ENNReal
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency)
open BinaryFractionalRows (Row)
open EncodedUnitCostReplication (Input selectedSet)
open RetainedGridState (Flags)
open RationalSparsestVertexRound (Result scaled round tree tapeBudget drawBound)
open RationalSparsestVertexThreshold (choose)
open RationalSparsestVertexExpectation (expectedSparsity)
open RationalSparsestEdgeRound (demandSet)
open FiniteDrawTrees (ideal)
open FiniteAmplification (probability)

attribute [local instance] EncodedUniformRounding.flagsFintype

def bad {n : ℕ} (D : Input n) (P : Finset (Fin n × Fin n)) (bound : ℝ)
    (result : Option (Flags n)) : Prop :=
  ∃ mask, result = some mask ∧ bound <
    (SparsestVertexBridge.sparsity D.graph D.cost P (selectedSet mask) : ℝ)

theorem probability_cost {n : ℕ} (D : Input n) (P : Finset (Fin n × Fin n))
    (mode : ChargedVertexModes.Mode) (T : ℕ) (bound : ℝ) (positive : 0 < bound)
    (expected : expectedSparsity D P mode ≤ bound) :
    probability ((EncodedSolverBits.fairTape (tapeBudget n T)).map
      (fun bits => (round D mode T bits).map Prod.fst)) (bad D P (2*bound)) ≤
        1/2+(drawBound n : ℝ)*((1 : ℝ)/2)^T := by
  let cost (mask : Flags n) : ℝ := SparsestVertexBridge.sparsity D.graph D.cost P (selectedSet mask)
  let event (mask : Flags n) : Prop := 2*bound < cost mask
  have pointwise (mask : Flags n) : bad D P (2*bound) (some mask) ↔ event mask := by
    constructor
    · rintro ⟨x, eq, paid⟩
      obtain rfl := Option.some.inj eq
      exact paid
    · exact fun paid => ⟨mask,rfl,paid⟩
  have measure :
      probability ((ideal (LazyFairBitTrees.lower T (tree D mode))).map some) (bad D P (2*bound)) =
        probability (ideal (LazyFairBitTrees.lower T (tree D mode))) event := by
    unfold probability
    rw [PMF.toOuterMeasure_map_apply]
    congr 2
    ext mask
    exact pointwise mask
  rw [RationalSparsestVertexRound.round_fairTape, measure]
  have finite : probability (ideal (LazyFairBitTrees.lower T (tree D mode))) event ≤
      probability (ideal (tree D mode)) event + (drawBound n : ℝ)*((1 : ℝ)/2)^T := by
    cases mode
    · exact EncodedWeightedRounding.bit_event_le T D event
    · exact EncodedSizeRounding.bit_event_le T D event
  refine finite.trans (add_le_add ?_ le_rfl)
  have markov := FiniteAmplification.threshold_mul_probability_le_expectedCost
    (ideal (tree D mode)) cost (fun _ => NNReal.coe_nonneg _) (2*bound) (by positivity)
  have compare : (2*bound)*probability (ideal (tree D mode)) event ≤ (2*bound)*(1/2) :=
    (markov.trans expected).trans_eq (by ring)
  exact le_of_mul_le_mul_left compare (by positivity)

def observe {n : ℕ} : Result n → Option (Flags n)
  | .cut mask _ => some mask
  | .zeroDistance => none

theorem observed {m n : ℕ} (A : Adjacency n) (w c : Row n) (P : Vector (Fin n × Fin n) m)
    {i : Fin m} {τ : ℚ≥0} (chosen : choose A w P = .threshold i τ)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (bits : Bits) :
    (RationalSparsestVertexRound.run A w c P mode T bits).bind observe =
      (round (scaled A w c τ) mode T bits).map Prod.fst := by
  simp only [RationalSparsestVertexRound.run, chosen]
  cases round (scaled A w c τ) mode T bits <;> rfl

theorem run_probability {m n : ℕ} (A : Adjacency n) (w c : Row n) (P : Vector (Fin n × Fin n) m)
    {i : Fin m} {τ : ℚ≥0} (chosen : choose A w P = .threshold i τ)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (bound : ℝ) (positive : 0 < bound)
    (expected : expectedSparsity (scaled A w c τ) (demandSet P) mode ≤ bound) :
    probability ((EncodedSolverBits.fairTape (tapeBudget n T)).map
      (fun bits => (RationalSparsestVertexRound.run A w c P mode T bits).bind observe))
      (bad (scaled A w c τ) (demandSet P) (2*bound)) ≤ 1/2+(drawBound n : ℝ)*((1 : ℝ)/2)^T := by
  simp only [observed A w c P chosen]
  exact probability_cost (scaled A w c τ) (demandSet P) mode T bound positive expected

end
end DirectedFlowCutGap.RationalSparsestVertexFairTape
