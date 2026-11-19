import DirectedFlowCutGap.PhysicalEdgeFamilyCost
import DirectedFlowCutGap.ChargedEdgeThresholdDemands

/-! Compute the original threshold demands once and keep them throughout
the actual adaptive edge calls. -/

namespace DirectedFlowCutGap.PhysicalPreparedEdgeFamily

open BinaryArithmetic RandomizedEdgeFamily CheckedMWHistory
open RationalEdgeDecomposition

structure Result (n : ℕ) where
  family : PhysicalEdgeFamily.Result n
  thresholdWork : ℕ

def run {n : ℕ} (D : Input n) (tape : Bits) : Option (Result n) :=
  if originalTotal D.adjacency D.weights < 1 then
    some ⟨⟨some ⟨fun _ => 1,List.replicate (rounds D) ∅⟩,tape,0,0,0⟩,0⟩
  else
    let table := ChargedEdgeThresholdDemands.demands D.adjacency D.weights
    (PhysicalEdgeFamily.runStages (PhysicalEdgeFamily.stepWith D table.1) (rounds D) (some initial) tape).map
      (fun history => ⟨history,table.2⟩)

theorem run_family {n : ℕ} (D : Input n) (tape : Bits) :
    (run D tape).map Result.family=PhysicalEdgeFamily.family D tape := by
  by_cases h : originalTotal D.adjacency D.weights < 1
  · simp only [run,PhysicalEdgeFamily.family,ite_eq_left h,Option.map_some]
  · let table := ChargedEdgeThresholdDemands.demands D.adjacency D.weights
    have stepEq : PhysicalEdgeFamily.stepWith D table.1 = PhysicalEdgeFamily.step D := by
      unfold table
      rw [ChargedEdgeThresholdDemands.demands_value]
      rfl
    rw [run,PhysicalEdgeFamily.family,ite_eq_right h,ite_eq_right h]
    change ((PhysicalEdgeFamily.runStages (PhysicalEdgeFamily.stepWith D table.1) (rounds D) (some initial) tape).map
      (fun r => (⟨r,table.2⟩ : Result n))).map Result.family = PhysicalEdgeFamily.run D tape
    rw [stepEq,Option.map_map]
    change (PhysicalEdgeFamily.run D tape).map id = PhysicalEdgeFamily.run D tape
    rw [Option.map_id,id_eq]

theorem run_observe {n : ℕ} (D : Input n) (tape : Bits) :
    (run D tape).map (fun r => r.family.observe)=
      (EncodedSolverBits.run (familyTree D) tape).map (fun (out,(rest,_)) => (out,rest)) := by
  rw [← PhysicalEdgeFamily.family_observe,← run_family,Option.map_map,Function.comp_def]

theorem threshold_paid {n B : ℕ} (D : Input n) (stored : AdaptiveWidthEnvelope.StoredWeights D.weights B)
    (tape : Bits) {out : Result n} (actual : run D tape=some out) :
    out.thresholdWork ≤ ChargedEdgeThresholdDemands.demandBudget n B := by
  by_cases h : originalTotal D.adjacency D.weights < 1
  · simp only [run,ite_eq_left h,Option.some.injEq] at actual
    rw [← actual]
    exact Nat.zero_le _
  · simp only [run,ite_eq_right h] at actual
    let table := ChargedEdgeThresholdDemands.demands D.adjacency D.weights
    change ((PhysicalEdgeFamily.runStages (PhysicalEdgeFamily.stepWith D table.1) (rounds D) (some initial) tape).map
      (fun history => ⟨history,table.2⟩))=some out at actual
    cases h : PhysicalEdgeFamily.runStages (PhysicalEdgeFamily.stepWith D table.1) (rounds D) (some initial) tape with
    | none => simp [h] at actual
    | some r =>
      simp only [h,Option.map_some,Option.some.injEq] at actual
      rw [← actual]
      exact ChargedEdgeThresholdDemands.demands_paid D.adjacency D.weights stored

theorem calibrated_paid {k : ℕ} (positive : 0<k) (M : ℕ) (multiplier : 0<M) :
    ∃ p : Polynomial ℕ, ∀ {n B : ℕ}, 0<n → ∀ (κ : ℕ)
      (adj : BinaryFractionalWalkOracle.Adjacency n) (w : RationalEdgeThresholds.Weights n),
      AdaptiveWidthEnvelope.StoredWeights w B → ∀ tape r, run (calibratedParameters k M κ adj w) tape=some r →
        PhysicalEdgeFamilyCost.paid r.family+r.thresholdWork ≤ p.eval (n+B+κ)+ChargedEdgeThresholdDemands.demandBudget n B := by
  obtain ⟨p,proof⟩ := PhysicalEdgeFamilyCost.calibrated_polynomial positive M multiplier
  refine ⟨p,?_⟩
  intro n B size κ adj w stored tape r runEq
  have same := run_family (calibratedParameters k M κ adj w) tape
  rw [runEq,Option.map_some] at same
  exact Nat.add_le_add (proof size κ adj w stored tape r.family same.symm) (threshold_paid _ stored tape runEq)

end DirectedFlowCutGap.PhysicalPreparedEdgeFamily
