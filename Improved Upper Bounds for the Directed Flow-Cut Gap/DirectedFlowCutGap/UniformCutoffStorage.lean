import DirectedFlowCutGap.CutoffArrayStorage
import DirectedFlowCutGap.PaidVertexRounding

/-! The uniform runner uses the concrete binary cutoff from its materialized
chain when the total is at least one. Otherwise it initializes an empty cut. -/
namespace DirectedFlowCutGap.UniformCutoffStorage

open BinaryArithmetic Polynomial EncodedArrayStorage
open EncodedUniformChain EncodedUniformWeightParameters EncodedUnitCostReplication RawNonnegativeRational
open PhysicalIntegerRoundingCost (eval_mono)

def Model {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) (code : List (Instruction Unit)) : Prop :=
  let ready := BinaryUniformArithmetic.compute D
  if (BinaryRawRational.le Code.one ready.1.total).1 then
    let level := BinaryUniformArithmetic.cutoff ready.1.average
    let chain := materializeWith ready.1.ports ready.1.average ready.1.counts level.1
    CutoffArrayStorage.Model T chain.data.adjacency chain.cutoff tape code
  else code=CutoffArrayStorage.constantMaskCode n ∧
    (PaidVertexRounding.uniform T D tape).1.map (fun r => (r.cut.mask,r.cut.suffix))=
      some (Vector.replicate n false,tape)

attribute [local irreducible] BinaryUniformArithmetic.compute materializeWith CutoffArrayStorage.Model in
set_option maxHeartbeats 2200000 in
theorem arrays : ∃ cells copies : Polynomial ℕ, ∀ {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits),
    ∃ code : List (Instruction Unit), Model T D tape code ∧
      fresh code ≤ cells.eval (n+T) ∧ code.length ≤ copies.eval (n+T) := by
  obtain ⟨cutCells,cutCopies,cutoff⟩ := CutoffArrayStorage.arrays
  let cells := cutCells.comp (6*X)+X+2
  let copies := cutCopies.comp (6*X)+X+3
  refine ⟨cells,copies,?_⟩
  intro n T D tape
  let ready := BinaryUniformArithmetic.compute D
  let level := BinaryUniformArithmetic.cutoff ready.1.average
  let chain := materializeWith ready.1.ports ready.1.average ready.1.counts level.1
  let test := BinaryRawRational.le Code.one ready.1.total
  have check : (BinaryRawRational.le Code.one (BinaryUniformArithmetic.compute D).1.total).1=test.1 := rfl
  cases active : test.1 with
  | false =>
      obtain ⟨space,work⟩ := CutoffArrayStorage.constant_layout n
      refine ⟨CutoffArrayStorage.constantMaskCode n,?_,?_,?_⟩
      · simp only [Model,PaidVertexRounding.uniform,check,active,Bool.false_eq_true,ite_false,Option.map_some,true_and]
      · rw [space]
        simp only [cells,eval_add,eval_X,eval_ofNat]
        omega
      · rw [work]
        simp only [copies,eval_add,eval_X,eval_ofNat]
        omega
  | true =>
      have exactData : ready.1=compute D := BinaryUniformArithmetic.compute_value D
      have positive : nontrivial D=true := by
        change (BinaryRawRational.le Code.one ready.1.total).1=true at active
        rw [BinaryRawRational.le_value,exactData] at active
        exact active
      have mass : 0<(compute D).total.realValue := by
        rw [compute_total]
        exact lt_of_lt_of_le (by norm_num) ((nontrivial_iff D).mp positive)
      have dim : chain.size ≤ 6*n := by
        change (materializeWith ready.1.ports ready.1.average ready.1.counts
          (BinaryUniformArithmetic.cutoff ready.1.average).1).size ≤ 6*n
        rw [BinaryUniformArithmetic.cutoff_value,exactData]
        exact expand_size_bound D mass
      obtain ⟨code,shape,space,work⟩ := cutoff T chain.data.adjacency chain.cutoff tape
      have index : chain.size+T ≤ (6*X : Polynomial ℕ).eval (n+T) := by
        simp only [eval_mul,eval_ofNat,eval_X]
        omega
      refine ⟨code,?_,?_,?_⟩
      · unfold Model
        dsimp only
        rw [check,ite_eq_left active]
        exact shape
      · rw [show cells.eval (n+T)=cutCells.eval ((6*X : Polynomial ℕ).eval (n+T))+(n+T)+2 by
          simp only [cells,eval_add,eval_comp,eval_X,eval_ofNat]]
        exact ((space.trans (eval_mono cutCells index)).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
      · rw [show copies.eval (n+T)=cutCopies.eval ((6*X : Polynomial ℕ).eval (n+T))+(n+T)+3 by
          simp only [copies,eval_add,eval_comp,eval_X,eval_ofNat]]
        exact ((work.trans (eval_mono cutCopies index)).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)

end DirectedFlowCutGap.UniformCutoffStorage
