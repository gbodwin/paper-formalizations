import DirectedFlowCutGap.ConcurrentEdgeCappedPrices
import DirectedFlowCutGap.NormalizedOptimalSelected

/-! Compose the bounded joint-path iteration with the original edge tape
rounder. The size guarantee compares directly to any normalized lengths. -/
namespace DirectedFlowCutGap.ConcurrentEdgeRound

open scoped BigOperators NNReal NNRat ENNReal
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open ConcurrentEdgeOracle (Edge)
open RationalSparsestEdgeRound (Mask Result scaled round tapeBudget drawBound demandSet)
open RationalSparsestEdgeThreshold (choose actualDistance)
open FiniteHarmonicThreshold (harmonicWeight)
open SparsestEdgeBridge (demandDistance)

variable {m n : ℕ}

def run (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits) : Option (Result n) :=
  RationalSparsestEdgeRound.run A (ConcurrentEdgeCappedPrices.solve hn A c P) c P mode T tape

theorem cut_valid (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (mode : ChargedVertexModes.Mode) (T : ℕ) {tape rest : Bits} {mask : Mask n}
    (ran : run hn A c P mode T tape = some (.cut mask rest)) :
    EncodedEdgeRounding.selectedEdges mask ⊆ graphEdges (graph A) ∧
      0 < (SparsestEdgeBridge.separated (graph A) (demandSet P)
        (EncodedEdgeRounding.selectedEdges mask)).card :=
  RationalSparsestEdgeRound.run_cut A _ c P mode T ran

private theorem entry (P : Vector (Edge n) m) (i : Fin m) : P.get i = P[i.val] := by
  cases i
  rfl

theorem computed_threshold (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (reachable : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) :
    ∃ i τ, choose A (ConcurrentEdgeCappedPrices.solve hn A c P) P = .threshold i τ := by
  let w := ConcurrentEdgeCappedPrices.solve hn A c P
  have normalized := (ConcurrentEdgeCappedPrices.solve_spec hn A c P reachable d different (fun _ => m)
    (NormalizedOptimalSelected.normalized_of_distinct_endpoints A P d (reachable d) different)).1
  have spec := RationalSparsestEdgeThreshold.choose_spec A w P
  cases found : choose A w P with
  | unreachable j =>
    rw [found] at spec
    have path := reachable j
    rw [entry P j] at path
    exact (((edgeDistance_eq_top_iff (graph A) (weights w) _ _).mp spec) path).elim
  | zero =>
    rw [found] at spec
    have zero (j : Fin m) : demandDistance (graph A) (weights w) (P.get j) = 0 := by
      rw [entry P j]
      simpa only [demandDistance, ENNReal.toNNReal_zero] using congrArg ENNReal.toNNReal (spec j)
    change (m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) (weights w) (P.get j) at normalized
    have pos : (0 : ℝ≥0) < m := by exact_mod_cast (Nat.zero_le _).trans_lt d.isLt
    simp only [zero, Finset.sum_const_zero] at normalized
    exact ((not_le_of_gt pos) normalized).elim
  | threshold i τ => exact ⟨i,τ,rfl⟩

theorem complete (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits)
    (reachable : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) (enough : tapeBudget n T ≤ tape.length) :
    ∃ cut used, run hn A c P mode T tape = some (.cut cut (tape.drop used)) ∧ used ≤ tapeBudget n T := by
  obtain ⟨i,τ,chosen⟩ := computed_threshold hn A c P reachable d different
  obtain ⟨cut,used,done,bound⟩ := RationalSparsestEdgeRound.round_complete
    (scaled A (ConcurrentEdgeCappedPrices.solve hn A c P) c τ) mode T tape enough
  exact ⟨cut,used,by simp only [run,RationalSparsestEdgeRound.run,chosen,done,Option.map_some],bound⟩

def observe {n : ℕ} : Result n → Option (Mask n)
  | .cut mask _ => some mask
  | .zeroDistance => none

theorem observed (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {i : Fin m} {τ : ℚ≥0} (chosen : choose A (ConcurrentEdgeCappedPrices.solve hn A c P) P = .threshold i τ)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (bits : Bits) :
    (run hn A c P mode T bits).bind observe =
      (round (scaled A (ConcurrentEdgeCappedPrices.solve hn A c P) c τ) mode T bits).map Prod.fst := by
  simp only [run, RationalSparsestEdgeRound.run, chosen]
  cases round (scaled A (ConcurrentEdgeCappedPrices.solve hn A c P) c τ) mode T bits <;> rfl

theorem size_probability :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ {m n : ℕ} (hn : 0 < n) (A : Adjacency n)
      (c : Weights n) (P : Vector (Edge n) m)
      (_distinct : Function.Injective fun j : Fin m => P[j.val])
      (_reachable : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
      (d : Fin m) (_different : (P.get d).1 ≠ (P.get d).2)
      (w : Edge n → ℝ≥0)
      (_normal : (m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) w (P.get j))
      (_price : 0 < weightedEdgeCost (graph A) (weights c) w)
      {i : Fin m} {τ : ℚ≥0}, choose A (ConcurrentEdgeCappedPrices.solve hn A c P) P = .threshold i τ →
      ∀ T : ℕ,
        let B := K * (n : ℝ)^(1/3+ε) * (harmonicWeight m : ℝ) *
          ((weightedEdgeCost (graph A) (weights c) w : ℝ)/(m : ℝ))
        FiniteAmplification.probability ((EncodedSolverBits.fairTape (tapeBudget n T)).map
          (fun bits => (run hn A c P .size T bits).bind observe))
          (RationalSparsestFairTape.bad (scaled A (ConcurrentEdgeCappedPrices.solve hn A c P) c τ)
            (demandSet P) (2*B)) ≤ 1/2 + (drawBound n : ℝ)*((1 : ℝ)/2)^T := by
  intro ε positive
  obtain ⟨K, Kpos, ideal⟩ := RationalSparsestEdgeExpectation.size_uniform ε positive
  refine ⟨6*K, by positivity, ?_⟩
  intro m n hn A c P distinct reachable d different w normalized price i τ chosen T
  let z := ConcurrentEdgeCappedPrices.solve hn A c P
  let D := scaled A z c τ
  let H : ℝ := harmonicWeight m
  let C : ℝ := weightedEdgeCost (graph A) (weights c) w
  let Cz : ℝ := weightedEdgeCost (graph A) (weights c) (weights z)
  let B := (6*K) * (n : ℝ)^(1/3+ε) * H * (C/(m : ℝ))
  let S : ℝ := ∑ j, (actualDistance A z P j : ℝ)
  have mpos : 0 < m := (Nat.zero_le _).trans_lt d.isLt
  have Hpos : 0 < H := NNReal.coe_pos.mpr (FiniteHarmonicThreshold.harmonicWeight_pos mpos)
  have Cpos : 0 < C := NNReal.coe_pos.mpr price
  have spec := ConcurrentEdgeCappedPrices.solve_spec hn A c P reachable d different w normalized
  have sum : (m : ℝ) ≤ S := by
    have cast := NNReal.coe_le_coe.mpr spec.1
    simpa only [NNReal.coe_natCast, NNReal.coe_sum, S, actualDistance, entry] using cast
  have ratio : Cz/S ≤ 6*C/(m : ℝ) := by
    have paid := div_le_div_of_nonneg_right spec.2 (show (0 : ℝ) ≤ m by positivity)
    exact (div_le_div_of_nonneg_left (NNReal.coe_nonneg _) (by exact_mod_cast mpos) sum).trans paid
  have expected : RationalSparsestEdgeExpectation.expectedSparsity D (demandSet P) .size ≤ B := by
    refine (ideal A z c P distinct chosen).trans ?_
    calc
      _ ≤ (K * (n : ℝ)^(1/3+ε) * H) * (6*C/(m : ℝ)) :=
        mul_le_mul_of_nonneg_left ratio (by positivity)
      _ = B := by unfold B; ring
  simp only [observed hn A c P chosen]
  exact RationalSparsestFairTape.probability_cost D (demandSet P) .size T B (by positivity) expected

theorem zero_cut_price (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (reachable : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2)
    (w : Edge n → ℝ≥0)
    (normalized : (m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) w (P.get j))
    (free : weightedEdgeCost (graph A) (weights c) w = 0)
    (mode : ChargedVertexModes.Mode) (T : ℕ) {bits rest : Bits} {mask : Mask n}
    (ran : run hn A c P mode T bits = some (.cut mask rest)) :
    edgeCutCost (graph A) (weights c) (EncodedEdgeRounding.selectedEdges mask) = 0 := by
  obtain ⟨i,τ,chosen⟩ := computed_threshold hn A c P reachable d different
  let z := ConcurrentEdgeCappedPrices.solve hn A c P
  let D := scaled A z c τ
  have cost := (ConcurrentEdgeCappedPrices.solve_spec hn A c P reachable d different w normalized).2
  rw [free, NNReal.coe_zero, mul_zero] at cost
  have zFree : weightedEdgeCost (graph A) (weights c) (weights z) = 0 :=
    NNReal.coe_eq_zero.mp (le_antisymm cost (NNReal.coe_nonneg _))
  have scaledFree : weightedEdgeCost D.graph D.cost D.weight = 0 := by
    change weightedEdgeCost (scaled A z c τ).graph (scaled A z c τ).cost (scaled A z c τ).weight = 0
    rw [RationalSparsestEdgeRound.scaled_graph, RationalSparsestEdgeRound.scaled_price,
      RationalSparsestEdgeRound.scaled_weight, SparsestEdgeBridge.weightedEdgeCost_div, zFree, zero_div]
  rw [run, RationalSparsestEdgeRound.run, chosen] at ran
  obtain ⟨⟨output,suffix⟩, performed, same⟩ := Option.map_eq_some_iff.mp ran
  obtain ⟨rfl,rfl⟩ := Result.cut.inj same
  simpa only [D,RationalSparsestEdgeRound.scaled_graph,RationalSparsestEdgeRound.scaled_price]
    using NormalizedOptimalZero.round_price_zero D mode T scaledFree performed

end DirectedFlowCutGap.ConcurrentEdgeRound
