import DirectedFlowCutGap.NormalizedOptimalMode
import DirectedFlowCutGap.NormalizedOptimalZero

/-! The computed mode gives the smaller finite-tape sparsity scale at one
uniform constant. Zero-cost optima give zero-cost cuts on every successful tape. -/
namespace DirectedFlowCutGap.NormalizedOptimalSelected

noncomputable section
open scoped BigOperators NNReal NNRat ENNReal
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalSparsestEdgeRound (Mask scaled tapeBudget drawBound demandSet)
open RationalSparsestEdgeExpectation (normalizedMass)
open RationalSparsestFairTape (bad)
open NormalizedOptimalSparsity (observedCut)
open NormalizedOptimalMode (runBest selected_run pick sizeScale massScale)
open FiniteAmplification (probability)
open EncodedEdgeRounding (selectedEdges)

private theorem probability_bad_le {n : ℕ} (D : EncodedEdgeGadget.Input n) (P : Finset (Fin n × Fin n))
    (p : PMF (Option (Mask n))) {a b : ℝ} (h : a ≤ b) :
    probability p (bad D P (2*b)) ≤ probability p (bad D P (2*a)) := by
  unfold probability
  apply ENNReal.toReal_mono _ (p.toOuterMeasure.mono ?_)
  · change p.toOuterMeasure {result | bad D P (2*a) result} ≠ ⊤
    rw [PMF.toOuterMeasure_apply]
    exact p.tsum_coe_indicator_ne_top _
  · rintro result ⟨mask, same, cost⟩
    exact ⟨mask, same, (mul_le_mul_of_nonneg_left h (by norm_num)).trans_lt cost⟩

theorem probability_bound :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ {m n : ℕ} (A : Adjacency n) (c : Weights n)
      (pairs : Vector (Fin n × Fin n) m)
      (_distinct : Function.Injective fun j : Fin m => pairs[j.val])
      (_reachable : ∀ j : Fin m, Nonempty (SimplePath (graph A) pairs[j.val].1 pairs[j.val].2))
      {q : ℚ} {w : Weights n}, 0 < q →
      NormalizedEdgeLP.minimize A c pairs.get (m : ℚ≥0) = some (q,w) →
      ∀ {i : Fin m} {τ : ℚ≥0}, RationalSparsestEdgeThreshold.choose A w pairs = .threshold i τ →
      ∀ T : ℕ,
        let B := K * (n : ℝ)^ε * min (sizeScale n m) (massScale m (normalizedMass A w pairs)) *
          ((q : ℝ)/(m : ℝ))
        probability ((EncodedSolverBits.fairTape (tapeBudget n T)).map
          (fun bits => (runBest A c pairs T bits).bind observedCut))
          (bad (scaled A w c τ) (demandSet pairs) (2*B)) ≤
            1/2+(drawBound n : ℝ)*((1 : ℝ)/2)^T := by
  intro ε positive
  obtain ⟨Ks,Kspos,size⟩ := NormalizedOptimalSparsity.optimal_size_probability ε positive
  obtain ⟨Km,Kmpos,mass⟩ := NormalizedOptimalSparsity.optimal_mass_probability ε positive
  let K := max Ks Km
  refine ⟨K, Kspos.trans_le (le_max_left _ _), ?_⟩
  intro m n A c pairs distinct reachable q w qpos optimum i τ threshold T
  let D := scaled A w c τ
  let P := demandSet pairs
  let W := normalizedMass A w pairs
  let S := sizeScale n m
  let M := massScale m W
  let price : ℝ := (q : ℝ)/(m : ℝ)
  let B := K * (n : ℝ)^ε * min S M * price
  have nonnegativePrice : 0 ≤ price := by
    apply div_nonneg
    · exact_mod_cast qpos.le
    · positivity
  have choice := NormalizedOptimalMode.pick_minimum A w pairs
  change probability ((EncodedSolverBits.fairTape (tapeBudget n T)).map
    (fun bits => (runBest A c pairs T bits).bind observedCut)) (bad D P (2*B)) ≤ _
  simp only [selected_run A c pairs T _ optimum]
  cases selected : pick A w pairs with
  | mass =>
    have bounds : M ≤ S := by
      rw [selected] at choice
      exact choice
    have paid : Km * (n : ℝ)^ε * M * price ≤ B := by
      change Km * (n : ℝ)^ε * M * price ≤ K * (n : ℝ)^ε * min S M * price
      rw [min_eq_right bounds]
      have nonnegativeMass : 0 ≤ M := by unfold M massScale; positivity
      gcongr
      exact le_max_right Ks Km
    refine (probability_bad_le D P _ paid).trans ?_
    simpa only [D, P, W, M, price, massScale, mul_assoc]
      using mass A c pairs distinct reachable qpos optimum threshold T
  | size =>
    have bounds : S ≤ M := by
      rw [selected] at choice
      exact choice
    have paid : Ks * (n : ℝ)^ε * S * price ≤ B := by
      change Ks * (n : ℝ)^ε * S * price ≤ K * (n : ℝ)^ε * min S M * price
      rw [min_eq_left bounds]
      have nonnegativeSize : 0 ≤ S := by unfold S sizeScale; positivity
      gcongr
      exact le_max_left Ks Km
    refine (probability_bad_le D P _ paid).trans ?_
    simpa only [D, P, S, price, sizeScale, Real.rpow_add_of_nonneg
      (by positivity : (0 : ℝ) ≤ n) (by norm_num : 0 ≤ (1/3 : ℝ)) positive.le,
      mul_comm, mul_left_comm, mul_assoc]
      using size A c pairs distinct reachable qpos optimum threshold T

theorem zero_price {m n : ℕ} (A : Adjacency n) (c : Weights n)
    (pairs : Vector (Fin n × Fin n) m)
    (reachable : ∀ j : Fin m, Nonempty (SimplePath (graph A) pairs[j.val].1 pairs[j.val].2))
    (T : ℕ) {tape rest : Bits} {mask : Mask n}
    (ran : runBest A c pairs T tape = some (0,.cut mask rest)) :
    edgeCutCost (graph A) (weights c) (selectedEdges mask) = 0 := by
  obtain ⟨⟨q,w⟩, solved, _⟩ := Option.bind_eq_some_iff.mp ran
  rw [selected_run A c pairs T tape solved] at ran
  exact NormalizedOptimalZero.optimal_cut_price_zero A c pairs reachable (pick A w pairs) T ran

theorem cut_valid {m n : ℕ} (A : Adjacency n) (c : Weights n)
    (pairs : Vector (Fin n × Fin n) m) (T : ℕ) {tape rest : Bits} {mask : Mask n} {price : ℚ}
    (ran : runBest A c pairs T tape = some (price,.cut mask rest)) :
    selectedEdges mask ⊆ graphEdges (graph A) ∧
      0 < (SparsestEdgeBridge.separated (graph A) (demandSet pairs) (selectedEdges mask)).card := by
  obtain ⟨⟨q,w⟩, solved, _⟩ := Option.bind_eq_some_iff.mp ran
  rw [selected_run A c pairs T tape solved] at ran
  exact NormalizedEdgeLPRound.optimal_cut_valid A c pairs (pick A w pairs) T ran

theorem complete {m n : ℕ} (A : Adjacency n) (c : Weights n)
    (pairs : Vector (Fin n × Fin n) m) (T : ℕ) (tape : Bits)
    (demanded : 0 < m)
    (reachable : ∀ j : Fin m, Nonempty (SimplePath (graph A) pairs[j.val].1 pairs[j.val].2))
    (enough : tapeBudget n T ≤ tape.length)
    (w : Fin n × Fin n → ℝ≥0)
    (normalized : (m : ℝ≥0) ≤ ∑ j : Fin m, SparsestEdgeBridge.demandDistance (graph A) w (pairs.get j)) :
    ∃ price mask used,
      runBest A c pairs T tape = some (price,.cut mask (tape.drop used)) ∧
      used ≤ tapeBudget n T ∧
      ∀ other : Fin n × Fin n → ℝ≥0,
        (m : ℝ≥0) ≤ ∑ j : Fin m, SparsestEdgeBridge.demandDistance (graph A) other (pairs.get j) →
          (price : ℝ) ≤ (weightedEdgeCost (graph A) (weights c) other : ℝ) := by
  have found := NormalizedEdgeLP.minimize_complete A c pairs.get
    (m : ℚ≥0) w reachable (by simpa only [NNRat.cast_natCast] using normalized)
  cases solved : NormalizedEdgeLP.minimize A c pairs.get (m : ℚ≥0) with
  | none => simp only [solved, Option.isSome_none, Bool.false_eq_true] at found
  | some answer =>
    obtain ⟨price,lengths⟩ := answer
    rw [selected_run A c pairs T tape solved]
    exact NormalizedEdgeLPRound.optimal_complete A c pairs (pick A lengths pairs) T tape
      demanded reachable enough w normalized

theorem normalized_of_distinct_endpoints {m n : ℕ} (A : Adjacency n)
    (pairs : Vector (Fin n × Fin n) m) (i : Fin m)
    (reachable : Nonempty (SimplePath (graph A) (pairs.get i).1 (pairs.get i).2))
    (different : (pairs.get i).1 ≠ (pairs.get i).2) :
    (m : ℝ≥0) ≤ ∑ j : Fin m,
      SparsestEdgeBridge.demandDistance (graph A) (fun _ => m) (pairs.get j) := by
  let w : Fin n × Fin n → ℝ≥0 := fun _ => m
  let s := (pairs.get i).1
  let t := (pairs.get i).2
  have lower : ((m : ℝ≥0) : ℝ≥0∞) ≤ edgeDistance (graph A) w s t := by
    apply (coe_le_edgeDistance_iff (graph A) w s t _).mpr
    intro path
    have long : 0 < path.edgeLength := by
      by_contra! short
      have zero : path.edgeLength = 0 := Nat.eq_zero_of_le_zero short
      have same : (0 : Fin (path.edgeLength+1)) = Fin.last path.edgeLength :=
        Fin.ext (by simp [zero])
      exact different (path.source_eq.symm.trans ((congrArg path.vertex same).trans path.target_eq))
    exact Finset.single_le_sum (f := w) (fun _ _ => zero_le) (path.edgeAt_mem_edges ⟨0,long⟩)
  have finite : edgeDistance (graph A) w s t ≠ ⊤ :=
    fun empty => ((edgeDistance_eq_top_iff (graph A) w s t).mp empty) reachable
  have entry : (m : ℝ≥0) ≤ SparsestEdgeBridge.demandDistance (graph A) w (pairs.get i) := by
    rw [← ENNReal.coe_toNNReal finite] at lower
    exact ENNReal.coe_le_coe.mp lower
  apply entry.trans
  exact Finset.single_le_sum
    (f := fun j : Fin m => SparsestEdgeBridge.demandDistance (graph A) w (pairs.get j))
    (fun _ _ => zero_le) (Finset.mem_univ i)

theorem complete_of_demand {m n : ℕ} (A : Adjacency n) (c : Weights n)
    (pairs : Vector (Fin n × Fin n) m) (T : ℕ) (tape : Bits) (i : Fin m)
    (reachable : ∀ j : Fin m, Nonempty (SimplePath (graph A) pairs[j.val].1 pairs[j.val].2))
    (different : (pairs.get i).1 ≠ (pairs.get i).2)
    (enough : tapeBudget n T ≤ tape.length) :
    ∃ price mask used, runBest A c pairs T tape = some (price,.cut mask (tape.drop used)) ∧
      used ≤ tapeBudget n T ∧
      ∀ other : Fin n × Fin n → ℝ≥0,
        (m : ℝ≥0) ≤ ∑ j : Fin m, SparsestEdgeBridge.demandDistance (graph A) other (pairs.get j) →
          (price : ℝ) ≤ (weightedEdgeCost (graph A) (weights c) other : ℝ) := by
  have reached : Nonempty (SimplePath (graph A) (pairs.get i).1 (pairs.get i).2) := by
    have entry : pairs.get i = pairs[i.val] := by
      cases i
      rfl
    rw [entry]
    exact reachable i
  exact complete A c pairs T tape (Nat.zero_le _ |>.trans_lt i.isLt) reachable enough
    (fun _ => m) (normalized_of_distinct_endpoints A pairs i reached different)

end
end DirectedFlowCutGap.NormalizedOptimalSelected
