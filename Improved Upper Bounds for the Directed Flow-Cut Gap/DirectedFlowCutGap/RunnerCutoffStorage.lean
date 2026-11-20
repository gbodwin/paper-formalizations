import DirectedFlowCutGap.UniformCutoffStorage

/-! The cutoff charge follows the actual port and replica reductions. Zero
objective returns before a cutoff, in either measured vertex mode. -/
namespace DirectedFlowCutGap.RunnerCutoffStorage

open BinaryArithmetic Polynomial EncodedArrayStorage EncodedUnitCostReplication
open PhysicalIntegerRoundingCost (eval_mono)

def WeightedModel {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) (code : List (Instruction Unit)) : Prop :=
  let pre := (BinaryPortPreparation.prepareAndReduce D).1
  match pre.reduced with
  | .zero _ _ => code=[]
  | .replicated _ _ replica _ => UniformCutoffStorage.Model T replica.input tape code

def Model {n : ℕ} (mode : ChargedVertexModes.Mode) (T : ℕ) (D : Input n)
    (tape : Bits) (code : List (Instruction Unit)) : Prop :=
  match mode with
  | .mass => WeightedModel T D tape code
  | .size => WeightedModel T (BinaryHeavyPreparation.prepare D).1.1.data tape code

open EncodedUnitCostPreparation in
attribute [local irreducible] BinaryPortPreparation.prepareAndReduce EncodedUnitCostPreparation.build UniformCutoffStorage.Model in
set_option maxHeartbeats 1200000 in
private theorem weighted_arrays : ∃ cells copies : Polynomial ℕ, ∀ {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits),
    ∃ code : List (Instruction Unit), WeightedModel T D tape code ∧
      fresh code ≤ cells.eval (n+T) ∧ code.length ≤ copies.eval (n+T) := by
  obtain ⟨p,q,bound⟩ := UniformCutoffStorage.arrays
  let pad : Polynomial ℕ := 4*X^2+X
  refine ⟨p.comp pad,q.comp pad,?_⟩
  intro n T D tape
  let pre := build D
  unfold WeightedModel
  rw [BinaryPortPreparation.prepareAndReduce_value]
  dsimp only
  rw [show (prepareAndReduce D).reduced=pre.data.reduce from rfl]
  by_cases zero : pre.data.totals.objective.num=0
  · rw [Input.reduce_zero _ zero]
    exact ⟨[],rfl,Nat.zero_le _,Nat.zero_le _⟩
  · rw [Input.reduce_positive _ zero]
    have positive : 0<n := by
      by_contra empty
      obtain rfl : n=0 := by omega
      exact zero (empty_objective_zero D)
    let replica := materialize pre.data pre.data.counts
    have limit : (cloneList pre.data.counts).length ≤ 4*n^2 := build_clone_count D positive zero
    have padded : (cloneList pre.data.counts).length+T ≤ pad.eval (n+T) := by
      simp only [pad,eval_add,eval_mul,eval_pow,eval_ofNat,eval_X]
      have grown := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.le_add_right n T) 2)
      exact (Nat.add_le_add_right limit T).trans (Nat.add_le_add grown (Nat.le_add_left _ _))
    obtain ⟨code,modeled,cellCount,copyCount⟩ := bound T replica.input tape
    refine ⟨code,modeled,?_,?_⟩
    · rw [eval_comp]
      exact cellCount.trans (eval_mono p padded)
    · rw [eval_comp]
      exact copyCount.trans (eval_mono q padded)

theorem arrays : ∃ cells copies : Polynomial ℕ, ∀ {n : ℕ} (mode : ChargedVertexModes.Mode) (T : ℕ)
    (D : Input n) (tape : Bits), ∃ code : List (Instruction Unit), Model mode T D tape code ∧
      fresh code ≤ cells.eval (n+T) ∧ code.length ≤ copies.eval (n+T) := by
  obtain ⟨cells,copies,weighted⟩ := weighted_arrays
  refine ⟨cells,copies,?_⟩
  intro n mode T D tape
  cases mode with
  | mass => exact weighted T D tape
  | size =>
    let prep := BinaryHeavyPreparation.prepare D
    have h : prep.1=EncodedHeavyVertexPreparation.prepare D := BinaryHeavyPreparation.prepare_value D
    have dim : prep.1.1.size ≤ n := h.symm ▸
      EncodedHeavyVertexPreparation.build_size_le D (EncodedCubeRootThreshold.threshold n)
    obtain ⟨code,modeled,space,work⟩ := weighted T prep.1.1.data tape
    have index := Nat.add_le_add_right dim T
    exact ⟨code,modeled,space.trans (eval_mono cells index),work.trans (eval_mono copies index)⟩

end DirectedFlowCutGap.RunnerCutoffStorage
