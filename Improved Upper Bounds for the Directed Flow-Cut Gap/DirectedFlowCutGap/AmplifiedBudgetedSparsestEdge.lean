import DirectedFlowCutGap.AmplifiedSparsestEdgeTape

/-! Compute rational budget candidates once and amplify the selected
sparsest-edge mode at its computed harmonic threshold. -/
namespace DirectedFlowCutGap.AmplifiedBudgetedSparsestEdge

open scoped BigOperators NNReal NNRat ENNReal
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeZeroPrices (detect freeLength)
open ConcurrentEdgeBudgetRound (prepare prepare_complete positive_threshold)
open ConcurrentEdgeBudgetSelection (Plan scale)
open RationalSparsestEdgeRound (Mask scaled demandSet tree)
open RationalSparsestEdgeThreshold (choose)
open RationalSparsestEdgeExpectation (expectedSparsity)
open SparsestEdgeBridge (demandDistance)
open AmplifiedSparsestEdgeTape (budget)
open EncodedEdgeRounding (selectedEdges)
open FiniteDrawTrees (ideal)

variable {m n : ℕ}

def run (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) : Option (Mask n × Bits) :=
  (prepare hn A c P).bind fun (w,mode) =>
    match choose A w P with
    | .threshold _ τ => AmplifiedSparsestEdgeTape.round A c P (scaled A w c τ) mode extra confidence bits
    | _ => none

theorem complete (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2)
    (extra confidence : ℕ) (bits : Bits) (enough : budget n extra confidence ≤ bits.length) :
    ∃ mask used, run hn A c P extra confidence bits = some (mask,bits.drop used) ∧
      used ≤ budget n extra confidence := by
  obtain ⟨w,mode,found,normal⟩ := prepare_complete hn A c P reach d different
  obtain ⟨i,τ,threshold⟩ := positive_threshold A w P d reach normal
  obtain ⟨mask,used,played,within⟩ := AmplifiedSparsestEdgeTape.complete A c P (scaled A w c τ)
    mode extra confidence bits enough
  exact ⟨mask,used,by simp only [run,found,Option.bind_some,threshold,played],within⟩

private theorem support_cut (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode)
    {mask : Mask n} (support : mask ∈ (ideal (tree D mode)).support) :
    selectedEdges mask ⊆ graphEdges D.graph ∧
      IsIntegralEdgeCut D.graph (selectedEdges mask) (edgeThresholdDemands D.graph D.weight) := by
  cases mode
  · exact EncodedEdgeRounding.support_valid D _ (fun I _ h => EncodedWeightedRounding.support_valid I h) support
  · exact EncodedEdgeRounding.support_valid D _ (fun I _ h => EncodedSizeRounding.support_valid I h) support

theorem cut_valid (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (distinct : Function.Injective fun j : Fin m => P[j.val]) (extra confidence : ℕ)
    {bits rest : Bits} {mask : Mask n}
    (ran : run hn A c P extra confidence bits = some (mask,rest)) :
    selectedEdges mask ⊆ graphEdges (graph A) ∧
      0 < (SparsestEdgeBridge.separated (graph A) (demandSet P) (selectedEdges mask)).card := by
  obtain ⟨⟨w,mode⟩,found,done⟩ := Option.bind_eq_some_iff.mp ran
  cases threshold : choose A w P with
  | unreachable => simp [threshold] at done
  | zero => simp [threshold] at done
  | threshold i τ =>
    simp only [threshold] at done
    obtain ⟨arcs,valid⟩ := support_cut (scaled A w c τ) mode
      (AmplifiedSparsestEdgeTape.supported A c P _ mode extra confidence done)
    have spec := RationalSparsestEdgeThreshold.choose_spec A w P
    rw [threshold] at spec
    exact ⟨arcs,spec.2.2.2.1.trans_le (RationalSparsestEdgeRound.count_le A w c P distinct threshold valid)⟩

noncomputable section
open FiniteAmplification (expectedCost probability)
open NormalizedOptimalMode (sizeScale massScale)
open FiniteHarmonicThreshold (harmonicWeight)

private theorem price_zero_on_support (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode)
    (zero : weightedEdgeCost D.graph D.cost D.weight = 0) {mask : Mask n}
    (support : mask ∈ (ideal (tree D mode)).support) :
    edgeCutCost D.graph D.cost (selectedEdges mask) = 0 := by
  let p := RationalSparsestEdgeExpectation.law D mode
  let cost (X : Finset (Edge n)) : ℝ := edgeCutCost D.graph D.cost X
  have expected : expectedCost p cost ≤ 0 := by
    change EncodedEdgeRounding.expectedPrice D (fun r => ChargedVertexModes.round r mode) ≤ 0
    cases mode
    · obtain ⟨_,_,bound⟩ := EncodedEdgeRounding.mass_expected_uniform 1 zero_lt_one
      simpa only [ChargedVertexModes.round,zero,NNReal.coe_zero,mul_zero] using bound n D
    · obtain ⟨_,_,bound⟩ := EncodedEdgeRounding.size_expected_uniform 1 zero_lt_one
      simpa only [ChargedVertexModes.round,zero,NNReal.coe_zero,mul_zero] using bound n D
  have seen : selectedEdges mask ∈ p.support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨mask,support,rfl⟩
  exact NNReal.coe_eq_zero.mp (FiniteAmplification.cost_eq_zero_on_support p cost
    (fun _ => NNReal.coe_nonneg _) expected seen)

theorem free_cut (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {j : Fin m} (test : detect A c P = some j) (extra confidence : ℕ)
    {bits rest : Bits} {mask : Mask n} (ran : run hn A c P extra confidence bits = some (mask,rest)) :
    edgeCutCost (graph A) (weights c) (selectedEdges mask) = 0 := by
  simp only [run,prepare,test,Option.bind_some] at ran
  let w := freeLength c m
  change (match choose A w P with
    | .threshold _ τ => AmplifiedSparsestEdgeTape.round A c P (scaled A w c τ) .mass extra confidence bits
    | _ => none) = some (mask,rest) at ran
  cases threshold : choose A w P with
  | unreachable => simp [threshold] at ran
  | zero => simp [threshold] at ran
  | threshold i τ =>
    simp only [threshold] at ran
    have free : weightedEdgeCost (scaled A w c τ).graph (scaled A w c τ).cost (scaled A w c τ).weight = 0 := by
      rw [RationalSparsestEdgeRound.scaled_graph, RationalSparsestEdgeRound.scaled_price,
        RationalSparsestEdgeRound.scaled_weight, SparsestEdgeBridge.weightedEdgeCost_div,
        ConcurrentEdgeZeroPrices.free_objective A c m, zero_div]
    simpa only [RationalSparsestEdgeRound.scaled_graph,RationalSparsestEdgeRound.scaled_price]
      using price_zero_on_support (scaled A w c τ) .mass free
      (AmplifiedSparsestEdgeTape.supported A c P _ .mass extra confidence ran)

def bad (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (B : ℝ) (result : Option (Mask n)) : Prop :=
  ∃ mask, result = some mask ∧
    B < (SparsestEdgeBridge.sparsity (graph A) (weights c) (demandSet P) (selectedEdges mask) : ℝ)

theorem failure : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ {m n : ℕ} (hn : 0 < n)
    (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (_distinct : Function.Injective fun j : Fin m => P[j.val])
    (_reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (d : Fin m) (_different : (P.get d).1 ≠ (P.get d).2)
    (w : Edge n → ℝ≥0) (_normal : (m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) w (P.get j))
    (mode : ChargedVertexModes.Mode) (extra confidence : ℕ),
      let B := K*(n : ℝ)^ε*
        scale n m (weightedEdgeCost (graph A) (weights c) w) (totalEdgeWeight (graph A) w) mode
      probability ((EncodedSolverBits.fairTape (budget n extra confidence)).map
        (fun bits => (run hn A c P extra confidence bits).map Prod.fst)) (bad A c P (2*B)) ≤
        ((1 : ℝ)/2)^(extra+1)+((1 : ℝ)/2)^confidence := by
  intro ε positive
  obtain ⟨K,Kpos,bound⟩ := ConcurrentEdgeBudgetRound.ideal_scale ε positive
  refine ⟨48*K, by positivity, ?_⟩
  intro m n hn A c P distinct reach d different w normal mode extra confidence
  let Cs := weightedEdgeCost (graph A) (weights c) w
  let Ws := totalEdgeWeight (graph A) w
  let B := (48*K)*(n : ℝ)^ε*scale n m Cs Ws mode
  have scaleNonneg : 0 ≤ scale n m Cs Ws mode := by
    cases mode <;> unfold scale sizeScale massScale <;> positivity
  have Bnonneg : 0 ≤ B := by unfold B; positivity
  cases test : detect A c P with
  | some j =>
    have impossible (bits : Bits) :
        ¬ bad A c P (2*B) ((run hn A c P extra confidence bits).map Prod.fst) := by
      rintro ⟨mask, output, paid⟩
      obtain ⟨⟨_,rest⟩,ran,same⟩ := Option.map_eq_some_iff.mp output
      dsimp only at same
      subst mask
      have free := free_cut hn A c P test extra confidence ran
      simp only [SparsestEdgeBridge.sparsity,free,zero_div,NNReal.coe_zero] at paid
      exact (not_lt_of_ge (by positivity : 0 ≤ 2*B)) paid
    have none : probability ((EncodedSolverBits.fairTape (budget n extra confidence)).map
        (fun bits => (run hn A c P extra confidence bits).map Prod.fst)) (bad A c P (2*B)) = 0 := by
      unfold probability
      rw [PMF.toOuterMeasure_map_apply]
      have empty : (fun bits => (run hn A c P extra confidence bits).map Prod.fst) ⁻¹'
          {x | bad A c P (2*B) x} = ∅ := by
        ext bits
        exact ⟨fun hit => (impossible bits hit).elim, fun hit => hit.elim⟩
      simp [empty]
    change probability _ (bad A c P (2*B)) ≤ _
    rw [none]
    positivity
  | none =>
    have positivePaths := ConcurrentEdgeZeroPrices.all_reachable test
    obtain ⟨z,found⟩ := ConcurrentEdgeBudgetSelection.has_choice hn A c P d different reach
      positivePaths w normal
    have good := ConcurrentEdgeBudgetSelection.chosen_normalized hn A c P found d different reach
    obtain ⟨i,τ,threshold⟩ := positive_threshold A z.lengths P d reach good
    let D := scaled A z.lengths c τ
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
    have Hpos : (0 : ℝ) < (harmonicWeight m : ℝ) := NNReal.coe_pos.mpr
      (FiniteHarmonicThreshold.harmonicWeight_pos mpos)
    have scalePos : 0 < scale n m Cs Ws mode := by
      cases mode <;> unfold scale sizeScale massScale <;> positivity
    have fail := AmplifiedSparsestEdgeTape.failure A c z.lengths P τ distinct z.mode extra confidence B
      (by unfold B; positivity) expected
    have observe (bits : Bits) : run hn A c P extra confidence bits =
        AmplifiedSparsestEdgeTape.round A c P D z.mode extra confidence bits := by
      simp only [run,prepare,test,found,Option.map_some,Option.bind_some,threshold,D]
    have event : bad A c P (2*B) = RationalSparsestFairTape.bad D (demandSet P) (2*B) := by
      funext result
      simp only [bad,RationalSparsestFairTape.bad,D,RationalSparsestEdgeRound.scaled_graph,
        RationalSparsestEdgeRound.scaled_price]
    have observed :
        (fun bits : Bits => (run hn A c P extra confidence bits).map Prod.fst) =
          (fun bits : Bits =>
            (AmplifiedSparsestEdgeTape.round A c P D z.mode extra confidence bits).map Prod.fst) := by
      funext bits
      rw [observe]
    change probability ((EncodedSolverBits.fairTape (budget n extra confidence)).map
      (fun bits => (run hn A c P extra confidence bits).map Prod.fst)) (bad A c P (2*B)) ≤ _
    rw [observed,event]
    exact fail

end
end DirectedFlowCutGap.AmplifiedBudgetedSparsestEdge
