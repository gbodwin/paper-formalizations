import DirectedFlowCutGap.VertexGraphArrayLayout
import DirectedFlowCutGap.BinaryUniformArithmetic

/-! Record the concrete uniform port, ratio and count arrays. Build the chain
arrays only on the same branch as the measured uniform runner. -/
namespace DirectedFlowCutGap.UniformPreparationArrays

open EncodedUnitCostReplication EncodedArrayStorage EncodedUniformChain Polynomial
open BinaryArrayNestedStorage (Code WithChildren Grid copyBudget cellBudget copyBudget_mono cellBudget_mono
  copyBudget_eval cellBudget_eval flat_bounds)
open ArrayMaterializationLayout (flat copyList)
open VertexGraphArrayLayout (Fields graphCode replicaCode graph_counts replica_counts)

def chainCode {n : ℕ} (D : Input n) : Code :=
  let p := (BinaryUniformArithmetic.compute D).1
  if (BinaryRawRational.le RawNonnegativeRational.Code.one p.total).1 then
    replicaCode (cloneList p.counts).length
  else []

def code {n : ℕ} (D : Input n) : Code := graphCode (3*n)++flat (3*n)++flat (3*n)++chainCode D

theorem parameters {n : ℕ} (D : Input n) :
    let p := (BinaryUniformArithmetic.compute D).1
    Fields p.ports ∧ WithChildren p.ratios (fun _ => []) (flat (3*n)) ∧
      WithChildren p.counts (fun _ => []) (flat (3*n)) := by
  dsimp only [BinaryUniformArithmetic.compute]
  refine ⟨⟨?_,?_,?_⟩,ArrayMaterializationLayout.batch _,ArrayMaterializationLayout.batch _⟩
  · exact ArrayMaterializationLayout.matrix _
  · exact ArrayMaterializationLayout.batch _
  · exact ArrayMaterializationLayout.replicate _ _

theorem chain {m : ℕ} (ports : Input m) (average : RawNonnegativeRational.Code) (counts : Vector ℕ m) (L : ℕ) :
    let out := materializeWith ports average counts L
    out.labels.toList=cloneList counts ∧
    CopyExec (cloneList counts) [] (cloneList counts).reverse (copyTrace (cloneList counts)) ∧
    ((reserveArray (cloneList counts).length++copyTrace (cloneList counts)).map PackedArraySchedule.shape : Code)=
      copyList out.size ∧ Fields out.data := by
  obtain ⟨copied,shape⟩ := ArrayMaterializationLayout.copy (cloneList counts)
  refine ⟨by simp [materializeWith,cloneList],copied,shape,⟨?_,?_,?_⟩⟩
  · exact ArrayMaterializationLayout.matrix _
  · exact ArrayMaterializationLayout.replicate _ _
  · exact ArrayMaterializationLayout.replicate _ _

open EncodedUniformWeightParameters in
private theorem chain_counts {n : ℕ} (D : Input n) :
    (chainCode D).length ≤ (6*n+3)*copyBudget (6*n)+4*(6*n)+4 ∧
    fresh (chainCode D) ≤ (6*n+3)*cellBudget (6*n)+6*n+2 := by
  let p := (BinaryUniformArithmetic.compute D).1
  unfold chainCode
  dsimp only
  split
  · rename_i active
    rw [BinaryRawRational.le_value,BinaryUniformArithmetic.compute_value] at active
    have positive : 0 < (compute D).total.realValue := by
      rw [compute_total]
      exact lt_of_lt_of_le (by norm_num) ((nontrivial_iff D).mp active)
    have size : (cloneList p.counts).length ≤ 6*n := by
      dsimp only [p]
      rw [BinaryUniformArithmetic.compute_value]
      exact clone_count D positive
    have range : (cloneList p.counts).length+3 ≤ 6*n+3 := Nat.add_le_add_right size _
    obtain ⟨copies,cells⟩ := replica_counts (cloneList p.counts).length
    exact ⟨copies.trans (by gcongr; exact copyBudget_mono size),
      cells.trans (by gcongr; exact cellBudget_mono size)⟩
  · exact ⟨Nat.zero_le _,Nat.zero_le _⟩

theorem polynomial : ∃ cells copies : Polynomial ℕ, ∀ {n : ℕ} (D : Input n),
    fresh (code D) ≤ cells.eval n ∧ (code D).length ≤ copies.eval n := by
  let p : Polynomial ℕ := 6*X
  let q : Polynomial ℕ := 3*X
  let cells := (q+5)*cellBudget q+((p+3)*cellBudget p+p+2)
  let copies := (q+5)*copyBudget q+((p+3)*copyBudget p+4*p+4)
  refine ⟨cells,copies,fun {n} D => ?_⟩
  obtain ⟨chainWork,chainSpace⟩ := chain_counts D
  obtain ⟨portWork,portSpace⟩ := graph_counts (3*n)
  obtain ⟨work,space⟩ : (flat (3*n)).length ≤ copyBudget (3*n) ∧
      fresh (flat (3*n)) ≤ cellBudget (3*n) := flat_bounds (3*n)
  simp only [code,fresh_append,List.length_append,cells,copies,eval_add,eval_mul,eval_ofNat,eval_X,
    cellBudget_eval,copyBudget_eval,p,q,Nat.add_mul] at chainWork chainSpace portWork portSpace ⊢
  constructor <;> omega

end DirectedFlowCutGap.UniformPreparationArrays
