import DirectedFlowCutGap.VertexPreparationBounds
import DirectedFlowCutGap.VertexReductionArrays
import DirectedFlowCutGap.UniformPreparationArrays
import DirectedFlowCutGap.RunnerCutoffStorage

/-! Place the selected mode's preparation arrays before the reached cutoff.
The zero objective and subunit-total branches skip the unused constructions. -/
namespace DirectedFlowCutGap.RunnerPreparationLayout

open EncodedUnitCostReplication EncodedArrayStorage Polynomial
open EncodedUnitCostPreparation (build prepareAndReduce build_size_le build_clone_count empty_objective_zero)
open BinaryArrayNestedStorage (Code copyBudget cellBudget copyBudget_mono cellBudget_mono
  copyBudget_eval cellBudget_eval)
open PhysicalIntegerRoundingCost (eval_mono)

def weightedCode {n : ℕ} (D : Input n) : Code :=
  let saved := (BinaryPortPreparation.prepareAndReduce D).1
  VertexPreparationArrays.portCode n saved.prepared.size++VertexReductionArrays.code saved.reduced++
    match saved.reduced with
    | .zero _ _ => []
    | .replicated _ _ clone _ => UniformPreparationArrays.code clone.input

def code {n : ℕ} (mode : ChargedVertexModes.Mode) (D : Input n) : Code :=
  match mode with
  | .mass => weightedCode D
  | .size =>
    let head := (BinaryHeavyPreparation.prepare D).1.1
    VertexPreparationArrays.heavyCode n head.size++weightedCode head.data

theorem weighted_reduction {n : ℕ} (D : Input n) :
    VertexReductionArrays.Model (BinaryPortPreparation.prepareAndReduce D).1.reduced :=
  VertexReductionArrays.arrays (BinaryPortPreparation.build D).1.data

private theorem replica_budget {n bound : ℕ} (inside : n≤bound) :
    (VertexGraphArrayLayout.replicaCode n).length ≤ (bound+3)*copyBudget bound+4*bound+4 ∧
      fresh (VertexGraphArrayLayout.replicaCode n) ≤ (bound+3)*cellBudget bound+bound+2 := by
  obtain ⟨work,space⟩ := VertexGraphArrayLayout.replica_counts n
  exact ⟨work.trans (by
    gcongr
    exact copyBudget_mono inside),
    space.trans (by
    gcongr
    exact cellBudget_mono inside)⟩

attribute [local irreducible] BinaryPortPreparation.prepareAndReduce EncodedUnitCostPreparation.build in
set_option maxHeartbeats 2000000 in
private theorem weighted_polynomial : ∃ cells copies : Polynomial ℕ, ∀ {n : ℕ} (D : Input n),
    fresh (weightedCode D) ≤ cells.eval n ∧ (weightedCode D).length ≤ copies.eval n := by
  obtain ⟨uniformCells,uniformCopies,uniform⟩ := UniformPreparationArrays.polynomial
  let p : Polynomial ℕ := 4*X^2+3*X
  let portCells := (4*p+10)*cellBudget p+p+2
  let portCopies := (4*p+10)*copyBudget p+4*p+4
  let reduceCells := (p+5)*cellBudget p+p+2
  let reduceCopies := (p+5)*copyBudget p+4*p+4
  let cells := portCells+reduceCells+uniformCells.comp p
  let copies := portCopies+reduceCopies+uniformCopies.comp p
  refine ⟨cells,copies,fun {n} D => ?_⟩
  let B := p.eval n
  have val : B=4*n^2+3*n := by simp only [B,p,eval_add,eval_mul,eval_pow,eval_ofNat,eval_X]
  have portInside : 3*n ≤ B := by rw [val]; omega
  let pre := build D
  have dim : pre.size ≤ B := (build_size_le D).trans portInside
  unfold weightedCode
  rw [BinaryPortPreparation.prepareAndReduce_value]
  dsimp only [prepareAndReduce]
  have port := VertexPreparationBounds.port portInside dim
  let after := pre.data.reduce
  have reduce :
      (VertexReductionArrays.code after).length ≤ (B+5)*copyBudget B+4*B+4 ∧
        fresh (VertexReductionArrays.code after) ≤ (B+5)*cellBudget B+B+2 := by
    obtain ⟨work,space⟩ := VertexPreparationBounds.flat_le dim
    by_cases zero : pre.data.totals.objective.num=0
    · simp only [after,Input.reduce_zero _ zero,VertexReductionArrays.code,Nat.add_mul]
      constructor <;> omega
    · have nPos : 0<n := by
        by_contra empty
        obtain rfl : n=0 := by omega
        exact zero (empty_objective_zero D)
      let count := (cloneList pre.data.counts).length
      have sized : count ≤ B := by
        rw [val]
        exact (build_clone_count D nPos zero).trans (Nat.le_add_right _ _)
      obtain ⟨replicaWork,replicaSpace⟩ := replica_budget sized
      simp only [after,Input.reduce_positive _ zero,VertexReductionArrays.code,List.length_append,
        fresh_append,count,Input.counts,Nat.add_mul] at replicaWork replicaSpace ⊢
      constructor <;> omega
  let extra := match after with
    | .zero _ _ => []
    | .replicated _ _ clone _ => UniformPreparationArrays.code clone.input
  have later : fresh extra ≤ uniformCells.eval B ∧ extra.length ≤ uniformCopies.eval B := by
    by_cases zero : pre.data.totals.objective.num=0
    · rw [show extra=[] by simp only [extra,after,Input.reduce_zero _ zero]]
      exact ⟨Nat.zero_le _,Nat.zero_le _⟩
    · have nPos : 0<n := by
        by_contra empty
        obtain rfl : n=0 := by omega
        exact zero (empty_objective_zero D)
      let clone := materialize pre.data pre.data.counts
      have sized : (cloneList pre.data.counts).length ≤ B := by
        rw [val]
        exact (build_clone_count D nPos zero).trans (Nat.le_add_right _ _)
      have ⟨space,work⟩ := uniform clone.input
      simp only [extra,after,Input.reduce_positive _ zero]
      exact ⟨space.trans (eval_mono _ sized),work.trans (eval_mono _ sized)⟩
  have space := Nat.add_le_add port.2 (Nat.add_le_add reduce.2 later.1)
  have work := Nat.add_le_add port.1 (Nat.add_le_add reduce.1 later.2)
  cases outcome : (build D).data.reduce
  all_goals
    constructor
    · simpa only [pre,after,extra,outcome,fresh_append,cells,portCells,reduceCells,eval_add,eval_mul,
        eval_comp,eval_ofNat,cellBudget_eval,B,Nat.add_assoc] using space
    · simpa only [pre,after,extra,outcome,List.length_append,copies,portCopies,reduceCopies,eval_add,
        eval_mul,eval_comp,eval_ofNat,copyBudget_eval,B,Nat.add_assoc] using work

set_option maxHeartbeats 1600000 in
theorem polynomial : ∃ cells copies : Polynomial ℕ,
    ∀ {n : ℕ} (mode : ChargedVertexModes.Mode) (D : Input n),
    fresh (code mode D) ≤ cells.eval n ∧ (code mode D).length ≤ copies.eval n := by
  obtain ⟨childCells,childCopies,weighted⟩ := weighted_polynomial
  let heavyCells : Polynomial ℕ := (X+6)*cellBudget X+X+2
  let heavyCopies : Polynomial ℕ := (X+6)*copyBudget X+4*X+4
  refine ⟨heavyCells+childCells,heavyCopies+childCopies,?_⟩
  intro n mode D
  cases mode with
  | mass =>
    obtain ⟨space,work⟩ := weighted D
    exact ⟨space.trans (by rw [eval_add]; exact Nat.le_add_left _ _),
      work.trans (by rw [eval_add]; exact Nat.le_add_left _ _)⟩
  | size =>
    let prep := (BinaryHeavyPreparation.prepare D).1.1
    have h : prep.size ≤ n := by
      change (BinaryHeavyPreparation.prepare D).1.1.size ≤ n
      rw [BinaryHeavyPreparation.prepare_value]
      exact EncodedHeavyVertexPreparation.build_size_le D (EncodedCubeRootThreshold.threshold n)
    obtain ⟨headWork,headSpace⟩ := VertexPreparationBounds.heavy (Nat.le_refl n) h
    obtain ⟨tailSpace,tailWork⟩ := weighted prep.data
    simp only [code,fresh_append,List.length_append,eval_add,heavyCells,heavyCopies,eval_mul,
      cellBudget_eval,copyBudget_eval,eval_X,eval_ofNat]
    exact ⟨Nat.add_le_add headSpace (tailSpace.trans (eval_mono _ h)),
      Nat.add_le_add headWork (tailWork.trans (eval_mono _ h))⟩

def Model {n : ℕ} (mode : ChargedVertexModes.Mode) (T : ℕ) (D : Input n) (tape : BinaryArithmetic.Bits)
    (trace : Code) : Prop :=
  ∃ cutoff, RunnerCutoffStorage.Model mode T D tape cutoff ∧ trace=code mode D++cutoff

theorem arrays : ∃ cells copies : Polynomial ℕ,
    ∀ {n : ℕ} (mode : ChargedVertexModes.Mode) (T : ℕ) (D : Input n) (tape : BinaryArithmetic.Bits),
    ∃ trace : Code, Model mode T D tape trace ∧ fresh trace ≤ cells.eval (n+T) ∧
      trace.length ≤ copies.eval (n+T) := by
  obtain ⟨prepCells,prepCopies,prepare⟩ := polynomial
  obtain ⟨cutCells,cutCopies,cut⟩ := RunnerCutoffStorage.arrays
  refine ⟨prepCells+cutCells,prepCopies+cutCopies,?_⟩
  intro n mode T D tape
  obtain ⟨space,work⟩ := prepare mode D
  obtain ⟨cutoff,run,used,steps⟩ := cut mode T D tape
  refine ⟨code mode D++cutoff,⟨cutoff,run,rfl⟩,?_,?_⟩
  · simp only [fresh_append,eval_add]
    exact Nat.add_le_add (space.trans (eval_mono _ (Nat.le_add_right _ _))) used
  · simp only [List.length_append,eval_add]
    exact Nat.add_le_add (work.trans (eval_mono _ (Nat.le_add_right _ _))) steps

end DirectedFlowCutGap.RunnerPreparationLayout
