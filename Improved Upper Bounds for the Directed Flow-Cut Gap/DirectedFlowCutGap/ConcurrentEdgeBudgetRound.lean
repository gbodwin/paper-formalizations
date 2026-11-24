import DirectedFlowCutGap.ConcurrentEdgeBudgetSelection
import DirectedFlowCutGap.ConcurrentEdgeRound

/-! Run the selected budgeted edge assignment on the original tape. -/
namespace DirectedFlowCutGap.ConcurrentEdgeBudgetRound

open scoped BigOperators NNReal NNRat ENNReal
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeBudgetSelection (Plan scale)
open ConcurrentEdgeZeroPrices (detect freeLength)
open RationalSparsestEdgeRound (Mask Result scaled round tapeBudget drawBound demandSet)
open RationalSparsestEdgeThreshold (choose actualDistance)
open SparsestEdgeBridge (demandDistance)
open FiniteHarmonicThreshold (harmonicWeight)

variable {m n : ℕ}

def prepare (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    Option (Weights n × ChargedVertexModes.Mode) :=
  match detect A c P with
  | some _ => some (freeLength c m,.mass)
  | none => (ConcurrentEdgeBudgetSelection.choose hn A c P).map fun p => (p.lengths,p.mode)

def run (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (T : ℕ) (bits : Bits) : Option (Result n) :=
  (prepare hn A c P).bind fun (w,mode) => RationalSparsestEdgeRound.run A w c P mode T bits

theorem prepare_complete (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) :
    ∃ w mode, prepare hn A c P = some (w,mode) ∧
      (m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) (weights w) (P.get j) := by
  cases test : detect A c P with
  | some j =>
    exact ⟨freeLength c m, .mass, by simp only [prepare,test],
      ConcurrentEdgeZeroPrices.free_normalized A c P j (reach j) (ConcurrentEdgeZeroPrices.detected test)⟩
  | none =>
    have normal := NormalizedOptimalSelected.normalized_of_distinct_endpoints A P d (reach d) different
    obtain ⟨plan,found⟩ := ConcurrentEdgeBudgetSelection.has_choice hn A c P d different reach
      (ConcurrentEdgeZeroPrices.all_reachable test) (fun _ => m) normal
    exact ⟨plan.lengths,plan.mode,by simp only [prepare,test,found,Option.map_some],
      ConcurrentEdgeBudgetSelection.chosen_normalized hn A c P found d different reach⟩

private theorem entry (P : Vector (Edge n) m) (i : Fin m) : P.get i = P[i.val] := by
  cases i
  rfl

theorem positive_threshold (A : Adjacency n) (w : Weights n) (P : Vector (Edge n) m) (d : Fin m)
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (normal : (m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) (weights w) (P.get j)) :
    ∃ i τ, choose A w P = .threshold i τ := by
  have spec := RationalSparsestEdgeThreshold.choose_spec A w P
  cases found : choose A w P with
  | unreachable i =>
    rw [found] at spec
    have reachable := reach i
    rw [entry P i] at reachable
    exact (((edgeDistance_eq_top_iff (graph A) (weights w) _ _).mp spec) reachable).elim
  | zero =>
    rw [found] at spec
    have zero (j : Fin m) : demandDistance (graph A) (weights w) (P.get j) = 0 := by
      rw [entry P j]
      simpa only [demandDistance, ENNReal.toNNReal_zero] using congrArg ENNReal.toNNReal (spec j)
    have count : (0 : ℝ≥0) < m := by exact_mod_cast (Nat.zero_le _).trans_lt d.isLt
    simp only [zero, Finset.sum_const_zero] at normal
    exact ((not_le_of_gt count) normal).elim
  | threshold i τ => exact ⟨i,τ,rfl⟩

theorem complete (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2)
    (T : ℕ) (bits : Bits) (enough : tapeBudget n T ≤ bits.length) :
    ∃ mask used, run hn A c P T bits = some (.cut mask (bits.drop used)) ∧ used ≤ tapeBudget n T := by
  obtain ⟨w,mode,found,normal⟩ := prepare_complete hn A c P reach d different
  obtain ⟨i,τ,threshold⟩ := positive_threshold A w P d reach normal
  obtain ⟨mask,used,played,within⟩ := RationalSparsestEdgeRound.round_complete
    (scaled A w c τ) mode T bits enough
  exact ⟨mask,used,by simp only [run,found,Option.bind_some,RationalSparsestEdgeRound.run,threshold,played,
    Option.map_some],within⟩

theorem cut_valid (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (T : ℕ) {bits rest : Bits} {mask : Mask n}
    (ran : run hn A c P T bits = some (.cut mask rest)) :
    EncodedEdgeRounding.selectedEdges mask ⊆ graphEdges (graph A) ∧
      0 < (SparsestEdgeBridge.separated (graph A) (demandSet P) (EncodedEdgeRounding.selectedEdges mask)).card := by
  obtain ⟨⟨w,mode⟩,_,done⟩ := Option.bind_eq_some_iff.mp ran
  exact RationalSparsestEdgeRound.run_cut A w c P mode T done

theorem free_cut (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) {j : Fin m} (test : detect A c P = some j)
    (T : ℕ) {bits rest : Bits} {mask : Mask n}
    (ran : run hn A c P T bits = some (.cut mask rest)) :
    edgeCutCost (graph A) (weights c) (EncodedEdgeRounding.selectedEdges mask) = 0 := by
  have norm := ConcurrentEdgeZeroPrices.free_normalized A c P j (reach j)
    (ConcurrentEdgeZeroPrices.detected test)
  apply ConcurrentEdgeRound.zero_cut_price hn A c P reach d different
    (weights (freeLength c m)) norm (ConcurrentEdgeZeroPrices.free_objective A c m) .mass T
  simpa only [run,prepare,test,Option.bind_some,ConcurrentEdgeRound.run,ConcurrentEdgeCappedPrices.solve]
    using ran

noncomputable section
open RationalSparsestEdgeExpectation (expectedSparsity normalizedMass)
open NormalizedOptimalMode (sizeScale massScale)
open FiniteAmplification (probability)

theorem ideal_scale :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ {m n : ℕ} (A : Adjacency n) (c w : Weights n)
      (P : Vector (Edge n) m) (_distinct : Function.Injective fun j : Fin m => P[j.val])
      (_normal : (m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) (weights w) (P.get j))
      {i : Fin m} {τ : ℚ≥0}, choose A w P = .threshold i τ →
      ∀ mode : ChargedVertexModes.Mode,
        expectedSparsity (scaled A w c τ) (demandSet P) mode ≤
          K * (n : ℝ)^ε * scale n m (weightedEdgeCost (graph A) (weights c) (weights w))
            (totalEdgeWeight (graph A) (weights w)) mode := by
  intro ε positive
  obtain ⟨Ks, sizePos, size⟩ := RationalSparsestEdgeExpectation.size_uniform ε positive
  obtain ⟨Km, massPos, mass⟩ := RationalSparsestEdgeExpectation.mass_uniform ε positive
  let K := max Ks Km
  have KsK : Ks ≤ K := le_max_left _ _
  have KmK : Km ≤ K := le_max_right _ _
  refine ⟨K, sizePos.trans_le KsK, ?_⟩
  intro m n A c w P distinct normal i τ selected mode
  let W := totalEdgeWeight (graph A) (weights w)
  let C := weightedEdgeCost (graph A) (weights c) (weights w)
  let S := ∑ j, actualDistance A w P j
  let H := (harmonicWeight m : ℝ)
  have mpos : (0 : ℝ≥0) < m := by exact_mod_cast (Nat.zero_le _).trans_lt i.isLt
  have sum : (m : ℝ≥0) ≤ S := by
    simpa only [S, actualDistance, entry] using normal
  have ratio : (C : ℝ)/(S : ℝ) ≤ (C : ℝ)/(m : ℝ) := by
    apply div_le_div_of_nonneg_left (NNReal.coe_nonneg _) (by exact_mod_cast mpos)
    exact_mod_cast sum
  have Wscaled : normalizedMass A w P ≤ W := by
    change (m : ℝ≥0)*W/S ≤ W
    rw [mul_comm, mul_div_assoc]
    exact mul_le_of_le_one_right zero_le ((div_le_one₀ (mpos.trans_le sum)).mpr sum)
  cases mode with
  | size =>
    calc
      _ ≤ Ks*(n : ℝ)^(1/3+ε)*H*((C : ℝ)/(S : ℝ)) := by
        simpa only [C, S, H, NNReal.coe_sum] using size A w c P distinct selected
      _ ≤ K*(n : ℝ)^(1/3+ε)*H*((C : ℝ)/(m : ℝ)) := by gcongr
      _ = _ := by
        simp only [scale, sizeScale]
        rw [Real.rpow_add_of_nonneg (by positivity : (0 : ℝ) ≤ n) (by norm_num : 0 ≤ (1/3 : ℝ)) positive.le]
        ring
  | mass =>
    have sqrt : (normalizedMass A w P : ℝ)^(1/2 : ℝ) ≤ (W : ℝ)^(1/2 : ℝ) :=
      Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr Wscaled) (by norm_num)
    calc
      _ ≤ Km*(n : ℝ)^ε*H^(3/2 : ℝ)*(normalizedMass A w P : ℝ)^(1/2 : ℝ)*((C : ℝ)/(S : ℝ)) := by
        simpa only [C, S, H, NNReal.coe_sum] using mass A w c P distinct selected
      _ ≤ K*(n : ℝ)^ε*H^(3/2 : ℝ)*(W : ℝ)^(1/2 : ℝ)*((C : ℝ)/(m : ℝ)) := by gcongr
      _ = _ := by simp only [scale,massScale]; ring

theorem observation (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (test : detect A c P = none) {z : Plan n} (found : ConcurrentEdgeBudgetSelection.choose hn A c P = some z)
    {i : Fin m} {τ : ℚ≥0} (threshold : choose A z.lengths P = .threshold i τ) (T : ℕ) (bits : Bits) :
    (run hn A c P T bits).bind ConcurrentEdgeRound.observe =
      (round (scaled A z.lengths c τ) z.mode T bits).map Prod.fst := by
  simp only [run, prepare, test, found, Option.map_some, Option.bind_some,
    RationalSparsestEdgeRound.run, threshold]
  cases round (scaled A z.lengths c τ) z.mode T bits <;> rfl

theorem probability_bound :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ {m n : ℕ} (hn : 0 < n) (A : Adjacency n)
      (c : Weights n) (P : Vector (Edge n) m)
      (_distinct : Function.Injective fun j : Fin m => P[j.val])
      (_reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
      (d : Fin m) (_different : (P.get d).1 ≠ (P.get d).2),
      detect A c P = none →
      ∀ {z : Plan n}, ConcurrentEdgeBudgetSelection.choose hn A c P = some z →
      ∀ {i : Fin m} {τ : ℚ≥0}, choose A z.lengths P = .threshold i τ →
      ∀ (w : Edge n → ℝ≥0),
        (m : ℝ≥0) ≤ (∑ j : Fin m, demandDistance (graph A) w (P.get j)) →
        ∀ (mode : ChargedVertexModes.Mode) (T : ℕ),
          let B := K * (n : ℝ)^ε *
            scale n m (weightedEdgeCost (graph A) (weights c) w) (totalEdgeWeight (graph A) w) mode
          probability ((EncodedSolverBits.fairTape (tapeBudget n T)).map
            (fun bits => (run hn A c P T bits).bind ConcurrentEdgeRound.observe))
            (RationalSparsestFairTape.bad (scaled A z.lengths c τ) (demandSet P) (2*B)) ≤
              1/2+(drawBound n : ℝ)*((1 : ℝ)/2)^T := by
  intro ε positive
  obtain ⟨K,Kpos,bound⟩ := ideal_scale ε positive
  refine ⟨48*K, by positivity, ?_⟩
  intro m n hn A c P distinct reach d different test z found i τ threshold w normal mode T
  let D := scaled A z.lengths c τ
  let Cs := weightedEdgeCost (graph A) (weights c) w
  let Ws := totalEdgeWeight (graph A) w
  let B := (48*K)*(n : ℝ)^ε*scale n m Cs Ws mode
  have good := ConcurrentEdgeBudgetSelection.chosen_normalized hn A c P found d different reach
  have positivePaths := ConcurrentEdgeZeroPrices.all_reachable test
  have compare := ConcurrentEdgeBudgetSelection.chosen_comparison hn A c P found d different reach
    positivePaths w normal mode
  have expected : expectedSparsity D (demandSet P) z.mode ≤ B := by
    refine (bound A c z.lengths P distinct good threshold z.mode).trans ?_
    have h := mul_le_mul_of_nonneg_left compare (show 0 ≤ K*(n : ℝ)^ε by positivity)
    exact h.trans_eq (by unfold B Cs Ws; ring)
  have Cpos : (0 : ℝ) < (Cs : ℝ) := NNReal.coe_pos.mpr
    ((by exact_mod_cast ConcurrentEdgeCappedPrices.floor_positive c : (0 : ℝ≥0) <
      (ConcurrentEdgeCappedPrices.floorPrice c : ℝ≥0)).trans_le
        (ConcurrentEdgeCappedPrices.floor_le_objective A c P d positivePaths w normal))
  have Wpos : (0 : ℝ) < (Ws : ℝ) :=
    NNReal.coe_pos.mpr (zero_lt_one.trans_le (ConcurrentEdgeBudgetGrid.normalized_mass_lower A P d reach w normal))
  have mpos : 0 < m := (Nat.zero_le _).trans_lt d.isLt
  have Hpos : (0 : ℝ) < (harmonicWeight m : ℝ) :=
    NNReal.coe_pos.mpr (FiniteHarmonicThreshold.harmonicWeight_pos mpos)
  have scalePos : 0 < scale n m Cs Ws mode := by
    cases mode <;> unfold scale sizeScale massScale <;> positivity
  simp only [observation hn A c P test found threshold]
  exact RationalSparsestFairTape.probability_cost D (demandSet P) z.mode T B (by positivity) expected

end
end DirectedFlowCutGap.ConcurrentEdgeBudgetRound
