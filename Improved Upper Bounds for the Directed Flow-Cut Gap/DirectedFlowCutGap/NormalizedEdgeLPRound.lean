import DirectedFlowCutGap.NormalizedEdgeLP
import DirectedFlowCutGap.RationalSparsestEdgeRound

/-! Compose the exact budget feasibility solver with the literal-tape
edge rounder. A positive number of reachable demands forces a positive
threshold on every feasible normalized witness. -/
namespace DirectedFlowCutGap.NormalizedEdgeLPRound

open scoped BigOperators NNReal NNRat ENNReal
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalSparsestEdgeRound (Mask Result round tapeBudget demandSet)
open EncodedEdgeRounding (selectedEdges)

def runAtBudget {m n : ℕ} (A : Adjacency n) (c : Weights n) (pairs : Vector (Fin n × Fin n) m)
    (budget : ℚ) (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits) : Option (Result n) :=
  (NormalizedEdgeLP.findWeights A c pairs.get (m : ℚ≥0) budget).bind
    fun w => RationalSparsestEdgeRound.run A w c pairs mode T tape

theorem cut_valid {m n : ℕ} (A : Adjacency n) (c : Weights n) (pairs : Vector (Fin n × Fin n) m)
    (budget : ℚ) (mode : ChargedVertexModes.Mode) (T : ℕ) {tape rest : Bits} {mask : Mask n}
    (ran : runAtBudget A c pairs budget mode T tape=some (.cut mask rest)) :
    selectedEdges mask ⊆ graphEdges (graph A) ∧
      0<(SparsestEdgeBridge.separated (graph A) (demandSet pairs) (selectedEdges mask)).card := by
  obtain ⟨w,_,result⟩ := Option.bind_eq_some_iff.mp ran
  exact RationalSparsestEdgeRound.run_cut A w c pairs mode T result

private theorem positive_threshold {m n : ℕ} (A : Adjacency n) (w : Weights n)
    (pairs : Vector (Fin n × Fin n) m) (demanded : 0 < m)
    (reachable : ∀ i : Fin m, Nonempty (SimplePath (graph A) pairs[i.val].1 pairs[i.val].2))
    (normalized : (m : ℝ≥0) ≤ ∑ i : Fin m, SparsestEdgeBridge.demandDistance (graph A) (weights w) (pairs.get i)) :
    ∃ i τ, RationalSparsestEdgeThreshold.choose A w pairs=.threshold i τ := by
  have spec := RationalSparsestEdgeThreshold.choose_spec A w pairs
  cases found : RationalSparsestEdgeThreshold.choose A w pairs with
  | unreachable i =>
    rw [found] at spec
    exact (((edgeDistance_eq_top_iff (graph A) (weights w) _ _).mp spec) (reachable i)).elim
  | zero =>
    rw [found] at spec
    have none (i : Fin m) : SparsestEdgeBridge.demandDistance (graph A) (weights w) (pairs.get i)=0 := by
      have entry : pairs[i.val] = pairs.get i := by
        cases i
        rfl
      simpa only [SparsestEdgeBridge.demandDistance, ← entry, ENNReal.toNNReal_zero]
        using congrArg ENNReal.toNNReal (spec i)
    have pos : (0 : ℝ≥0) < m := by exact_mod_cast demanded
    simp only [none,Finset.sum_const_zero] at normalized
    exact (not_le_of_gt pos normalized).elim
  | threshold i τ => exact ⟨i,τ,rfl⟩

attribute [local irreducible] NormalizedEdgeLP.findWeights in
set_option maxHeartbeats 1000000 in
theorem complete {m n : ℕ} (A : Adjacency n) (c : Weights n) (pairs : Vector (Fin n × Fin n) m)
    (budget : ℚ) (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits)
    (demanded : 0 < m) (reachable : ∀ i : Fin m, Nonempty (SimplePath (graph A) pairs[i.val].1 pairs[i.val].2))
    (enough : tapeBudget n T≤tape.length)
    (w : Fin n × Fin n → ℝ≥0)
    (normalized : (m : ℝ≥0) ≤ ∑ i : Fin m, SparsestEdgeBridge.demandDistance (graph A) w (pairs.get i))
    (affordable : (weightedEdgeCost (graph A) (weights c) w : ℝ)≤(budget : ℝ)) :
    ∃ mask used, runAtBudget A c pairs budget mode T tape=some (.cut mask (tape.drop used)) ∧
      used≤tapeBudget n T := by
  have witness := NormalizedEdgeLP.findWeights_complete A c pairs.get (m : ℚ≥0) budget w
    reachable (by simpa only [NNRat.cast_natCast] using normalized) affordable
  cases found : NormalizedEdgeLP.findWeights A c pairs.get (m : ℚ≥0) budget with
  | none => rw [found] at witness; cases witness
  | some optimum =>
    have valid := (NormalizedEdgeLP.findWeights_sound A c pairs.get (m : ℚ≥0) budget reachable found).1
    rw [NNRat.cast_natCast] at valid
    obtain ⟨i,τ,positive⟩ := positive_threshold A optimum pairs demanded reachable valid
    obtain ⟨mask,used,ran,charge⟩ := RationalSparsestEdgeRound.round_complete
      (RationalSparsestEdgeRound.scaled A optimum c τ) mode T tape enough
    refine ⟨mask,used,?_,charge⟩
    simp only [runAtBudget,found,Option.bind_some,RationalSparsestEdgeRound.run,positive,ran,Option.map_some]

def runOptimal {m n : ℕ} (A : Adjacency n) (c : Weights n) (pairs : Vector (Fin n × Fin n) m)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits) : Option (ℚ × Result n) :=
  (NormalizedEdgeLP.minimize A c pairs.get (m : ℚ≥0)).bind fun (q,w) =>
    (RationalSparsestEdgeRound.run A w c pairs mode T tape).map fun result => (q,result)

theorem optimal_cut_valid {m n : ℕ} (A : Adjacency n) (c : Weights n)
    (pairs : Vector (Fin n × Fin n) m) (mode : ChargedVertexModes.Mode) (T : ℕ)
    {tape rest : Bits} {mask : Mask n} {q : ℚ} (ran : runOptimal A c pairs mode T tape=some (q,.cut mask rest)) :
    selectedEdges mask ⊆ graphEdges (graph A) ∧
      0<(SparsestEdgeBridge.separated (graph A) (demandSet pairs) (selectedEdges mask)).card := by
  obtain ⟨⟨_,w⟩,_,mapped⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨output,played,same⟩ := Option.map_eq_some_iff.mp mapped
  have shape : output=.cut mask rest := congrArg Prod.snd same
  subst output
  exact RationalSparsestEdgeRound.run_cut A w c pairs mode T played

attribute [local irreducible] NormalizedEdgeLP.minimize in
set_option maxHeartbeats 1000000 in
theorem optimal_complete {m n : ℕ} (A : Adjacency n) (c : Weights n) (pairs : Vector (Fin n × Fin n) m)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits)
    (demanded : 0 < m) (reachable : ∀ i : Fin m, Nonempty (SimplePath (graph A) pairs[i.val].1 pairs[i.val].2))
    (enough : tapeBudget n T≤tape.length)
    (w : Fin n × Fin n → ℝ≥0)
    (normalized : (m : ℝ≥0) ≤ ∑ i : Fin m, SparsestEdgeBridge.demandDistance (graph A) w (pairs.get i)) :
    ∃ price mask used,
      runOptimal A c pairs mode T tape=some (price,.cut mask (tape.drop used)) ∧ used≤tapeBudget n T ∧
      ∀ other : Fin n × Fin n → ℝ≥0,
        (m : ℝ≥0)≤∑ i : Fin m, SparsestEdgeBridge.demandDistance (graph A) other (pairs.get i) →
          (price : ℝ)≤(weightedEdgeCost (graph A) (weights c) other : ℝ) := by
  have solved := NormalizedEdgeLP.minimize_complete A c pairs.get (m : ℚ≥0) w reachable
    (by simpa only [NNRat.cast_natCast] using normalized)
  cases found : NormalizedEdgeLP.minimize A c pairs.get (m : ℚ≥0) with
  | none => rw [found] at solved; cases solved
  | some output =>
    obtain ⟨price,optimum⟩ := output
    obtain ⟨valid,_,minimal⟩ := NormalizedEdgeLP.minimize_attained A c pairs.get (m : ℚ≥0) reachable found
    rw [NNRat.cast_natCast] at valid minimal
    obtain ⟨i,τ,positive⟩ := positive_threshold A optimum pairs demanded reachable valid
    obtain ⟨mask,used,ran,charge⟩ := RationalSparsestEdgeRound.round_complete
      (RationalSparsestEdgeRound.scaled A optimum c τ) mode T tape enough
    refine ⟨price,mask,used,?_,charge,minimal⟩
    simp only [runOptimal,found,Option.bind_some,RationalSparsestEdgeRound.run,positive,ran,Option.map_some]

end DirectedFlowCutGap.NormalizedEdgeLPRound
