import DirectedFlowCutGap.ConcurrentVertexBudgetSelection
import DirectedFlowCutGap.AmplifiedSparsestVertexTape
import DirectedFlowCutGap.NormalizedVertexLPRound

/-! Amplify the budget-selected vertex assignment using exact sparsity.
An available zero-price cut can be returned immediately. -/
namespace DirectedFlowCutGap.ConcurrentVertexBudgetRound

open scoped BigOperators NNReal NNRat
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency graph)
open BinaryFractionalRows (Row)
open ConcurrentEdgeOracle (Edge)
open RationalSparsestVertexDistances (weights)
open SparsestVertexBridge (demandDistance)
open EncodedUnitCostReplication (selectedSet)
open RetainedGridState (Flags)
open RationalSparsestEdgeRound (demandSet)
open RationalSparsestVertexThreshold (choose actualDistance)
open RationalSparsestVertexRound (scaled)
open RationalSparsestVertexExpectation (expectedSparsity normalizedMass)
open ConcurrentVertexBudget (freeMask freeDemand)
open ConcurrentVertexBudgetSelection (Plan)
open ConcurrentEdgeBudgetSelection (scale)
open AmplifiedSparsestVertexTape (budget round supported cut_support)
open FiniteHarmonicThreshold (harmonicWeight)

variable {m n : ℕ}

def run (hn : 0 < n) (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) : Option (Flags n × Bits) :=
  match freeDemand A c P with
  | some _ => some (freeMask c,bits)
  | none => (ConcurrentVertexBudgetSelection.choose hn A c P).bind fun z =>
    match choose A z.lengths P with
    | .threshold _ τ => round A c P (scaled A z.lengths c τ) z.mode extra confidence bits
    | _ => none

theorem complete (hn : 0 < n) (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    (reach : ∀ i : Fin m, Nonempty (SimplePath (graph A) (P.get i).1 (P.get i).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) (noArc : ¬ (graph A).Adj (P.get d).1 (P.get d).2)
    (extra confidence : ℕ) (bits : Bits) (enough : budget n extra confidence ≤ bits.length) :
    ∃ mask used, run hn A c P extra confidence bits = some (mask,bits.drop used) ∧
      used ≤ budget n extra confidence := by
  cases test : freeDemand A c P with
  | some i => exact ⟨freeMask c,0,by simp only [run,test,List.drop_zero],Nat.zero_le _⟩
  | none =>
    obtain ⟨z,selected⟩ := ConcurrentVertexBudgetSelection.has_choice hn A c P reach d different noArc test
    have normal := ConcurrentVertexBudgetSelection.chosen_normalized hn A c P selected reach d different noArc
    obtain ⟨i,τ,threshold⟩ := NormalizedVertexLPRound.positive_threshold A z.lengths P reach d normal
    obtain ⟨mask,used,ran,within⟩ := AmplifiedSparsestVertexTape.complete A c P
      (scaled A z.lengths c τ) z.mode extra confidence bits enough
    exact ⟨mask,used,by simp only [run,test,selected,Option.bind_some,threshold,ran],within⟩

private theorem entry (P : Vector (Edge n) m) (i : Fin m) : P.get i = P[i.val] := by cases i; rfl

theorem cut_valid (hn : 0 < n) (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    (distinct : Function.Injective fun j : Fin m => P[j.val]) (extra confidence : ℕ)
    {bits rest : Bits} {mask : Flags n}
    (ran : run hn A c P extra confidence bits = some (mask,rest)) :
    0 < (SparsestVertexBridge.separated (graph A) (demandSet P) (selectedSet mask)).card := by
  classical
  cases test : freeDemand A c P with
  | some d =>
    simp only [run,test,Option.some.injEq,Prod.mk.injEq] at ran
    obtain ⟨rfl,rfl⟩ := ran
    have requested : P.get d ∈ demandSet P := Finset.mem_image.mpr ⟨d,Finset.mem_univ _,(entry P d).symm⟩
    exact Finset.card_pos.mpr ⟨⟨P.get d,requested⟩,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,ConcurrentVertexBudget.free_found A c P test⟩⟩
  | none =>
    rw [run,test] at ran
    obtain ⟨z,_,after⟩ := Option.bind_eq_some_iff.mp ran
    cases threshold : choose A z.lengths P with
    | unreachable => simp [threshold] at after
    | zero => simp [threshold] at after
    | threshold i τ =>
      simp only [threshold] at after
      let D := scaled A z.lengths c τ
      have valid := cut_support D z.mode (supported A c P D z.mode extra confidence after)
      have spec := RationalSparsestVertexThreshold.choose_spec A z.lengths P
      rw [threshold] at spec
      exact spec.2.2.2.1.trans_le (RationalSparsestVertexRound.count_le A z.lengths c P distinct threshold valid)

theorem zero_cut (hn : 0 < n) (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    {i : Fin m} (test : freeDemand A c P = some i) (extra confidence : ℕ)
    {bits rest : Bits} {mask : Flags n} (ran : run hn A c P extra confidence bits = some (mask,rest)) :
    cutCost (weights c) (selectedSet mask) = 0 := by
  simp only [run,test,Option.some.injEq,Prod.mk.injEq] at ran
  obtain ⟨rfl,rfl⟩ := ran
  exact ConcurrentVertexBudget.free_zero c

noncomputable section
open FiniteAmplification (probability)
open NormalizedOptimalMode (sizeScale massScale)

private theorem scale_mono_mass (n m : ℕ) (C M W : ℝ≥0) (bound : M ≤ W) (mode : ChargedVertexModes.Mode) :
    scale n m C M mode ≤ scale n m C W mode := by
  cases mode with
  | size => exact le_rfl
  | mass =>
    unfold scale massScale
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr bound)
        (by norm_num)) (by positivity)) (by positivity)

private theorem normalized_mass_le (A : Adjacency n) (w : Row n) (P : Vector (Edge n) m) (i : Fin m)
    (normal : (m : ℝ≥0) ≤ ∑ j, actualDistance A w P j) :
    normalizedMass A w P ≤ totalWeight (weights w) := by
  have mpos : (0 : ℝ≥0) < m := by exact_mod_cast (Nat.zero_le _).trans_lt i.isLt
  unfold normalizedMass
  rw [mul_comm, mul_div_assoc]
  exact mul_le_of_le_one_right zero_le ((div_le_one₀ (mpos.trans_le normal)).mpr normal)

def bad (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m) (bound : ℝ) (out : Option (Flags n)) : Prop :=
  ∃ mask, out = some mask ∧
    bound < (SparsestVertexBridge.sparsity (graph A) (weights c) (demandSet P) (selectedSet mask) : ℝ)

theorem failure : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ {m n : ℕ} (hn : 0 < n)
    (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    (_distinct : Function.Injective fun j : Fin m => P[j.val])
    (_reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (d : Fin m) (_different : (P.get d).1 ≠ (P.get d).2) (_noArc : ¬ (graph A).Adj (P.get d).1 (P.get d).2)
    (w : Fin n → ℝ≥0) (_normal : (m : ℝ≥0) ≤ ∑ j, demandDistance (graph A) w (P.get j))
    (mode : ChargedVertexModes.Mode) (extra confidence : ℕ),
      let B := K*(n : ℝ)^ε * scale n m (weightedCost (weights c) w) (totalWeight w) mode
      probability ((EncodedSolverBits.fairTape (budget n extra confidence)).map
        (fun bits => (run hn A c P extra confidence bits).map Prod.fst)) (bad A c P (2*B)) ≤
        ((1 : ℝ)/2)^(extra+1)+((1 : ℝ)/2)^confidence := by
  intro ε positive
  obtain ⟨K,Kpos,bound⟩ := NormalizedVertexLPRound.ideal_bound ε positive
  refine ⟨48*K,by positivity,?_⟩
  intro m n hn A c P distinct reach d different noArc w normal mode extra confidence
  let Cs := weightedCost (weights c) w
  let Ws := totalWeight w
  let B := (48*K)*(n : ℝ)^ε*scale n m Cs Ws mode
  have nonneg : 0 ≤ B := mul_nonneg (by positivity) (ConcurrentEdgeBudgetSelection.scale_nonnegative ..)
  cases test : freeDemand A c P with
  | some i =>
    have impossible (bits : Bits) :
        ¬ bad A c P (2*B) ((run hn A c P extra confidence bits).map Prod.fst) := by
      rintro ⟨mask,returned,paid⟩
      obtain ⟨⟨_,rest⟩,ran,same⟩ := Option.map_eq_some_iff.mp returned
      dsimp only at same
      subst mask
      have zero := zero_cut hn A c P test extra confidence ran
      simp only [SparsestVertexBridge.sparsity,zero,zero_div,NNReal.coe_zero] at paid
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
    obtain ⟨z,selected⟩ := ConcurrentVertexBudgetSelection.has_choice hn A c P reach d different noArc test
    have good := ConcurrentVertexBudgetSelection.chosen_normalized hn A c P selected reach d different noArc
    obtain ⟨i,τ,threshold⟩ := NormalizedVertexLPRound.positive_threshold A z.lengths P reach d good
    let D := scaled A z.lengths c τ
    have norm : (m : ℝ≥0) ≤ ∑ j, actualDistance A z.lengths P j := by
      simpa only [actualDistance,← entry] using good
    have compare := ConcurrentVertexBudgetSelection.chosen_comparison hn A c P selected reach d different noArc
      test w normal mode
    have expected : expectedSparsity D (demandSet P) z.mode ≤ B := by
      refine (bound A z.lengths c P distinct norm threshold z.mode).trans ?_
      have raw := scale_mono_mass n m (weightedCost (weights c) (weights z.lengths)) _ _
        (normalized_mass_le A z.lengths P i norm) z.mode
      have h := mul_le_mul_of_nonneg_left (raw.trans compare) (show 0 ≤ K*(n : ℝ)^ε by positivity)
      exact h.trans_eq (by unfold B Cs Ws; ring)
    have Cpos : (0 : ℝ) < (Cs : ℝ) := NNReal.coe_pos.mpr
      ((by exact_mod_cast ConcurrentVertexBudget.floor_positive c : (0 : ℝ≥0) <
        (ConcurrentVertexBudget.floorPrice c : ℝ≥0)).trans_le
          (ConcurrentVertexBudget.floor_le_cost A c P d test w normal))
    have Wpos : (0 : ℝ) < (Ws : ℝ) :=
      NNReal.coe_pos.mpr (zero_lt_one.trans_le (ConcurrentVertexBudget.mass_lower A P d reach w normal))
    have mpos : 0 < m := (Nat.zero_le _).trans_lt d.isLt
    have Hpos : (0 : ℝ) < (harmonicWeight m : ℝ) := NNReal.coe_pos.mpr
      (FiniteHarmonicThreshold.harmonicWeight_pos mpos)
    have scalePos : 0 < scale n m Cs Ws mode := by
      cases mode <;> unfold scale sizeScale massScale <;> positivity
    have fail := AmplifiedSparsestVertexTape.failure A z.lengths c P τ distinct z.mode extra confidence B
      (by unfold B; positivity) expected
    have observed :
        (fun bits : Bits => (run hn A c P extra confidence bits).map Prod.fst) =
          (fun bits : Bits => (round A c P D z.mode extra confidence bits).map Prod.fst) := by
      funext bits
      simp only [run,test,selected,Option.bind_some,threshold,D]
    have event : bad A c P (2*B) = RationalSparsestVertexFairTape.bad D (demandSet P) (2*B) := by
      funext result
      simp only [bad,RationalSparsestVertexFairTape.bad,D,RationalSparsestVertexRound.scaled_graph,
        RationalSparsestVertexRound.scaled_price]
    change probability ((EncodedSolverBits.fairTape (budget n extra confidence)).map
      (fun bits => (run hn A c P extra confidence bits).map Prod.fst)) (bad A c P (2*B)) ≤ _
    rw [observed,event]
    exact fail

end
end DirectedFlowCutGap.ConcurrentVertexBudgetRound
